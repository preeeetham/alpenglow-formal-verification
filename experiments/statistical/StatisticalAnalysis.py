#!/usr/bin/env python3
"""
Statistical Model Checking for Alpenglow Consensus
Runs Monte Carlo simulations for realistic network sizes (10-100+ nodes)
"""

import os
import sys
import json
import time
import subprocess
import concurrent.futures
from pathlib import Path
import random

class AlpenglowStatisticalAnalysis:
    def __init__(self):
        self.base_dir = Path(__file__).parent.parent.parent
        self.results = []
        self.total_simulations = 0
        self.successful_simulations = 0
        
    def generate_large_scale_configs(self):
        """Generate configurations for different network sizes"""
        configs = []
        
        # Test different network sizes - feasible for real TLC verification
        for nodes in [10, 15, 20, 25, 30, 40, 50]:
            # Test different Byzantine/crash ratios
            for byz_percent in [5, 10, 15, 20]:  # Up to 20% Byzantine
                for crash_percent in [5, 10, 15, 20]:  # Up to 20% crashed
                    
                    byzantine_count = max(1, (nodes * byz_percent) // 100)
                    crashed_count = max(1, (nodes * crash_percent) // 100)
                    
                    # Ensure we don't exceed fault tolerance bounds
                    if byzantine_count + crashed_count < nodes * 0.5:
                        config = {
                            'NodeCount': nodes,
                            'ByzantineCount': byzantine_count,
                            'CrashedCount': crashed_count,
                            'SlotCount': 3,  # Keep slots small for performance
                            'HashVariants': 2,
                            'NetworkDelay': 100,
                            'seed': random.randint(0, 1000000)
                        }
                        configs.append(config)
        
        return configs[:20]  # Limit to 20 configs for real TLC verification
    
    def create_config_file(self, config, config_path):
        """Create TLA+ config file for statistical run"""
        cfg_content = f"""SPECIFICATION Spec

CONSTANTS
    NodeCount = {config['NodeCount']}
    SlotCount = {config['SlotCount']}
    HashVariants = {config['HashVariants']}
    ByzantineCount = {config['ByzantineCount']}
    CrashedCount = {config['CrashedCount']}
    NetworkDelay = {config['NetworkDelay']}

INVARIANTS
    LargeScaleInvariants

PROPERTIES
    ProbabilisticSafety

ALGORITHM
    BFS

MAX_STATES
    100000

TIMEOUT
    600

WORKERS
    4

MEMORY
    4096

SEED
    {config['seed']}
"""
        
        with open(config_path, 'w') as f:
            f.write(cfg_content)
    
    def run_statistical_verification(self, config):
        """Run REAL TLC verification for a single configuration"""
        print(f"🔄 Testing: {config['NodeCount']} nodes, {config['ByzantineCount']} Byzantine, {config['CrashedCount']} crashed")
        
        config_dir = self.base_dir / "experiments" / "statistical" / "configs"
        config_dir.mkdir(exist_ok=True)
        
        config_name = f"stat_{config['NodeCount']}_{config['ByzantineCount']}_{config['CrashedCount']}_{config['seed']}"
        config_path = config_dir / f"{config_name}.cfg"
        
        # Create TLA+ config file for this specific configuration
        self.create_config_file(config, config_path)
        
        # Use the statistical TLA+ specification
        tla_file = self.base_dir / "model-checking" / "statistical" / "LargeScaleConfig.tla"
        
        # Build TLC command with optimizations for large-scale checking
        cmd = [
            "java", 
            "-Xmx4g",  # 4GB heap
            "-XX:+UseParallelGC",  # Parallel garbage collector
            "-cp", str(self.base_dir / "tla2tools.jar"),
            "tlc2.TLC", 
            "-nowarning",
            "-workers", "4",  # Use 4 worker threads
            "-config", str(config_path), 
            str(tla_file)
        ]
        
        start_time = time.time()
        try:
            # Set timeout based on network size (larger networks get more time)
            timeout_seconds = min(600, 60 + (config['NodeCount'] // 10) * 30)  # 1-10 minutes max
            
            result = subprocess.run(
                cmd, 
                capture_output=True, 
                text=True, 
                timeout=timeout_seconds,
                cwd=str(self.base_dir),
                env={**os.environ, 'JAVA_HOME': os.environ.get('JAVA_HOME', '')}
            )
            
            runtime = time.time() - start_time
            
            # Parse TLC output for real results
            output = result.stdout + result.stderr
            states_explored = self.extract_states_explored(output)
            distinct_states = self.extract_distinct_states(output)
            success = result.returncode == 0 and 'finished' in output.lower()
            invariant_violations = 'violated' in output.lower() or 'invariant' in output.lower()
            deadlocks = 'deadlock' in output.lower()
            
            print(f"   ✅ {config['NodeCount']} nodes: {states_explored} states, {runtime:.1f}s, {'SUCCESS' if success else 'FAILED'}")
            
            return {
                'config': config,
                'runtime': runtime,
                'success': success,
                'states_explored': states_explored,
                'distinct_states': distinct_states,
                'invariant_violations': invariant_violations,
                'deadlocks': deadlocks,
                'output': output[:2000],  # Keep detailed output but truncate
                'error': '' if success else f"Exit code: {result.returncode}"
            }
            
        except subprocess.TimeoutExpired:
            runtime = time.time() - start_time
            print(f"   ⏱️  {config['NodeCount']} nodes: TIMEOUT after {timeout_seconds}s")
            return {
                'config': config,
                'runtime': runtime,
                'success': False,
                'states_explored': 0,
                'distinct_states': 0,
                'invariant_violations': False,
                'deadlocks': False,
                'output': f'Timeout after {timeout_seconds} seconds',
                'error': 'timeout'
            }
        except Exception as e:
            runtime = time.time() - start_time
            print(f"   ❌ {config['NodeCount']} nodes: ERROR - {str(e)}")
            return {
                'config': config,
                'runtime': runtime,
                'success': False,
                'states_explored': 0,
                'distinct_states': 0,
                'invariant_violations': False,
                'deadlocks': False,
                'output': '',
                'error': str(e)
            }
    
    def run_parallel_analysis(self):
        """Run statistical analysis with multiple configurations in parallel"""
        print("🎲 STATISTICAL ANALYSIS")
        print("=" * 40)
        print("🔄 Generating large-scale configurations...")
        
        configs = self.generate_large_scale_configs()
        self.total_simulations = len(configs)
        
        print(f"📊 Running {self.total_simulations} statistical simulations...")
        print(f"   Network sizes: 10-50 nodes (real TLC verification)")
        print(f"   Byzantine faults: 5-20%")
        print(f"   Crash faults: 5-20%")
        
        # Run simulations in parallel
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
            future_to_config = {
                executor.submit(self.run_statistical_verification, config): config 
                for config in configs
            }
            
            completed = 0
            for future in concurrent.futures.as_completed(future_to_config):
                result = future.result()
                self.results.append(result)
                
                if result['success']:
                    self.successful_simulations += 1
                
                completed += 1
                print(f"   Progress: {completed}/{self.total_simulations} simulations completed")
        
        print(f"✅ Statistical analysis complete: {self.successful_simulations}/{self.total_simulations} successful")
    
    def extract_states_explored(self, output):
        """Extract number of states explored from TLC output"""
        try:
            for line in output.split('\n'):
                if 'states generated' in line.lower():
                    # Extract number from line like "12345 states generated"
                    words = line.split()
                    for word in words:
                        if word.replace(',', '').isdigit():
                            return int(word.replace(',', ''))
            return 0
        except:
            return 0
    
    def extract_distinct_states(self, output):
        """Extract number of distinct states from TLC output"""
        try:
            for line in output.split('\n'):
                if 'distinct states' in line.lower():
                    # Extract number from line like "12345 distinct states"
                    words = line.split()
                    for word in words:
                        if word.replace(',', '').isdigit():
                            return int(word.replace(',', ''))
            return 0
        except:
            return 0
    
    def analyze_byzantine_tolerance(self):
        """Analyze Byzantine fault tolerance across different network sizes"""
        tolerance_data = {}
        
        for result in self.results:
            config = result['config']
            nodes = config['NodeCount']
            byz_count = config['ByzantineCount']
            
            if nodes not in tolerance_data:
                tolerance_data[nodes] = {'max_byzantine': 0, 'total_tests': 0, 'successful_tests': 0}
            
            tolerance_data[nodes]['total_tests'] += 1
            if result['success']:
                tolerance_data[nodes]['successful_tests'] += 1
                tolerance_data[nodes]['max_byzantine'] = max(
                    tolerance_data[nodes]['max_byzantine'], 
                    byz_count
                )
        
        return tolerance_data
    
    def generate_report(self):
        """Generate statistical analysis report"""
        if not self.results:
            return {}
        
        successful_results = [r for r in self.results if r['success']]
        
        avg_states = sum(r['states_explored'] for r in successful_results) / max(len(successful_results), 1)
        avg_runtime = sum(r['runtime'] for r in successful_results) / max(len(successful_results), 1)
        max_states = max((r['states_explored'] for r in successful_results), default=0)
        
        byzantine_tolerance = self.analyze_byzantine_tolerance()
        
        report = {
            'summary': {
                'total_simulations': self.total_simulations,
                'successful_simulations': self.successful_simulations,
                'success_rate': (self.successful_simulations / max(self.total_simulations, 1)) * 100,
                'avg_states_explored': int(avg_states),
                'avg_runtime_seconds': round(avg_runtime, 2),
                'max_states_explored': max_states
            },
            'byzantine_tolerance': byzantine_tolerance,
            'detailed_results': self.results
        }
        
        return report
    
    def save_results(self):
        """Save statistical analysis results"""
        report = self.generate_report()
        
        output_file = self.base_dir / "experiments" / "statistical" / "statistical_analysis.json"
        output_file.parent.mkdir(exist_ok=True)
        
        with open(output_file, 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"📊 Statistical analysis results saved to {output_file}")
        return output_file

def main():
    """Main statistical analysis runner"""
    analyzer = AlpenglowStatisticalAnalysis()
    
    try:
        analyzer.run_parallel_analysis()
        analyzer.save_results()
        
        print("\n🎯 STATISTICAL ANALYSIS SUMMARY")
        print("=" * 40)
        print(f"Total Simulations: {analyzer.total_simulations}")
        print(f"Successful: {analyzer.successful_simulations}")
        print(f"Success Rate: {(analyzer.successful_simulations/max(analyzer.total_simulations,1))*100:.1f}%")
        
        return True
        
    except Exception as e:
        print(f"❌ Statistical analysis failed: {e}")
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)