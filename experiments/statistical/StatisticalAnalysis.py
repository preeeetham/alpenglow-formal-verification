#!/usr/bin/env python3
"""
Alpenglow Consensus Statistical Analysis
Monte Carlo simulation and statistical validation for large-scale configurations
"""

import subprocess
import time
import json
import random
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
from pathlib import Path
from scipy import stats
import concurrent.futures

class StatisticalAnalyzer:
    def __init__(self):
        self.base_dir = Path(__file__).parent.parent.parent
        self.tla_tools = self.base_dir / "tla2tools.jar"
        self.results = []
        
    def generate_random_config(self, node_count, byzantine_count, crashed_count, seed=None):
        """Generate random configuration for Monte Carlo sampling"""
        if seed:
            random.seed(seed)
            
        # Select random Byzantine nodes
        all_nodes = list(range(1, node_count + 1))
        byzantine_nodes = random.sample(all_nodes, byzantine_count)
        
        # Select random crashed nodes (non-overlapping with Byzantine)
        remaining_nodes = [n for n in all_nodes if n not in byzantine_nodes]
        crashed_nodes = random.sample(remaining_nodes, crashed_count)
        
        config = {
            'NodeCount': node_count,
            'ByzantineCount': byzantine_count,
            'CrashedCount': crashed_count,
            'ByzantineNodes': byzantine_nodes,
            'CrashedNodes': crashed_nodes,
            'HonestNodes': [n for n in all_nodes if n not in byzantine_nodes + crashed_nodes],
            'seed': seed
        }
        
        return config
    
    def create_config_file(self, config, config_name):
        """Create TLC configuration file from config dict"""
        config_dir = self.base_dir / "experiments" / "statistical" / "configs"
        config_dir.mkdir(exist_ok=True)
        
        config_file = config_dir / f"{config_name}.cfg"
        
        content = f"""SPECIFICATION Spec

CONSTANTS
    NodeCount = {config['NodeCount']}
    SlotCount = 5
    HashVariants = 4
    ByzantineCount = {config['ByzantineCount']}
    CrashedCount = {config['CrashedCount']}
    NetworkDelay = 100
    StakeDistribution = "equal"

INVARIANTS
    LargeScaleInvariants

PROPERTIES
    ProbabilisticSafety
    ExpectedFinalizationTime

ALGORITHM
    BFS

MAX_STATES
    100000

TIMEOUT
    300

WORKERS
    4

MEMORY
    4096

SYMMETRY
    Permutations

COMPRESS
    TRUE

TRACE
    TRUE

COUNTEREXAMPLE
    TRUE

VERBOSE
    FALSE

SEED
    {config.get('seed', random.randint(1, 1000000))}
"""
        
        with open(config_file, 'w') as f:
            f.write(content)
            
        return config_file
    
    def run_single_simulation(self, config, spec_file):
        """Run single Monte Carlo simulation"""
        config_name = f"sim_{config['NodeCount']}_{config['ByzantineCount']}_{config['CrashedCount']}_{config['seed']}"
        config_file = self.create_config_file(config, config_name)
        
        start_time = time.time()
        
        cmd = [
            "java", "-cp", str(self.tla_tools),
            "tlc2.TLC", "-config", str(config_file), str(spec_file)
        ]
        
        try:
            result = subprocess.run(
                cmd,
                timeout=300,
                capture_output=True,
                text=True
            )
            
            end_time = time.time()
            runtime = end_time - start_time
            
            # Parse results
            simulation_result = {
                'config': config,
                'runtime': runtime,
                'success': result.returncode == 0,
                'states_explored': self.parse_states(result.stdout),
                'invariant_violations': 'violated' in result.stdout,
                'deadlocks': 'Deadlock' in result.stdout,
                'output': result.stdout,
                'error': result.stderr
            }
            
            return simulation_result
            
        except subprocess.TimeoutExpired:
            return {
                'config': config,
                'runtime': 300,
                'success': False,
                'states_explored': 0,
                'invariant_violations': False,
                'deadlocks': False,
                'timeout': True
            }
    
    def parse_states(self, output):
        """Parse number of states explored from TLC output"""
        import re
        pattern = r'(\d+) distinct states found'
        match = re.search(pattern, output)
        return int(match.group(1)) if match else 0
    
    def monte_carlo_simulation(self, node_counts, byzantine_ratios, crashed_ratios, num_samples=100):
        """Run Monte Carlo simulation across different configurations"""
        print("🎲 Running Monte Carlo Statistical Analysis...")
        
        spec_file = self.base_dir / "model-checking" / "statistical" / "LargeScaleConfig.tla"
        
        all_results = []
        
        for node_count in node_counts:
            print(f"  Testing {node_count} nodes...")
            
            for byzantine_ratio in byzantine_ratios:
                byzantine_count = int(node_count * byzantine_ratio / 100)
                if byzantine_count == 0:
                    continue
                    
                for crashed_ratio in crashed_ratios:
                    crashed_count = int(node_count * crashed_ratio / 100)
                    
                    # Ensure we don't exceed total nodes
                    if byzantine_count + crashed_count >= node_count:
                        continue
                    
                    print(f"    Byzantine: {byzantine_count}, Crashed: {crashed_count}")
                    
                    # Run multiple samples
                    sample_results = []
                    for sample in range(num_samples):
                        config = self.generate_random_config(
                            node_count, byzantine_count, crashed_count, 
                            seed=sample
                        )
                        
                        result = self.run_single_simulation(config, spec_file)
                        sample_results.append(result)
                        all_results.append(result)
                        
                        if sample % 10 == 0:
                            print(f"      Sample {sample}/{num_samples}")
                    
                    # Analyze this configuration
                    self.analyze_configuration(sample_results, node_count, byzantine_count, crashed_count)
        
        self.results = all_results
        return all_results
    
    def analyze_configuration(self, results, node_count, byzantine_count, crashed_count):
        """Analyze results for a specific configuration"""
        successful = [r for r in results if r['success']]
        failed = [r for r in results if not r['success']]
        
        if not successful:
            print(f"      ❌ All {len(results)} samples failed")
            return
        
        success_rate = len(successful) / len(results) * 100
        avg_states = np.mean([r['states_explored'] for r in successful])
        avg_runtime = np.mean([r['runtime'] for r in successful])
        
        print(f"      ✅ Success rate: {success_rate:.1f}% ({len(successful)}/{len(results)})")
        print(f"      📊 Avg states: {avg_states:.0f}, Avg runtime: {avg_runtime:.1f}s")
        
        # Check for safety violations
        violations = [r for r in results if r.get('invariant_violations', False)]
        if violations:
            print(f"      ⚠️  {len(violations)} safety violations detected!")
    
    def analyze_byzantine_tolerance(self):
        """Analyze Byzantine fault tolerance across different failure rates"""
        print("🛡️  Analyzing Byzantine Fault Tolerance...")
        
        byzantine_analysis = {}
        
        for result in self.results:
            if not result['success']:
                continue
                
            config = result['config']
            byzantine_ratio = (config['ByzantineCount'] / config['NodeCount']) * 100
            crashed_ratio = (config['CrashedCount'] / config['NodeCount']) * 100
            
            key = (config['NodeCount'], byzantine_ratio, crashed_ratio)
            
            if key not in byzantine_analysis:
                byzantine_analysis[key] = []
            
            byzantine_analysis[key].append({
                'success': result['success'],
                'violations': result.get('invariant_violations', False),
                'states': result['states_explored']
            })
        
        # Calculate success rates
        tolerance_analysis = {}
        for key, results in byzantine_analysis.items():
            node_count, byzantine_ratio, crashed_ratio = key
            success_rate = sum(1 for r in results if r['success']) / len(results)
            violation_rate = sum(1 for r in results if r['violations']) / len(results)
            
            tolerance_analysis[key] = {
                'success_rate': success_rate,
                'violation_rate': violation_rate,
                'sample_count': len(results)
            }
        
        return tolerance_analysis
    
    def generate_statistical_report(self):
        """Generate comprehensive statistical analysis report"""
        print("📊 Generating Statistical Analysis Report...")
        
        if not self.results:
            print("  No results to analyze")
            return
        
        df = pd.DataFrame(self.results)
        
        # Basic statistics
        total_simulations = len(df)
        successful_simulations = len(df[df['success'] == True])
        success_rate = successful_simulations / total_simulations * 100
        
        # Byzantine tolerance analysis
        byzantine_analysis = self.analyze_byzantine_tolerance()
        
        # Performance analysis
        successful_df = df[df['success'] == True]
        if not successful_df.empty:
            avg_states = successful_df['states_explored'].mean()
            avg_runtime = successful_df['runtime'].mean()
            max_states = successful_df['states_explored'].max()
        else:
            avg_states = avg_runtime = max_states = 0
        
        report = {
            'summary': {
                'total_simulations': total_simulations,
                'successful_simulations': successful_simulations,
                'success_rate': success_rate,
                'avg_states_explored': avg_states,
                'avg_runtime_seconds': avg_runtime,
                'max_states_explored': max_states
            },
            'byzantine_tolerance': byzantine_analysis,
            'detailed_results': self.results
        }
        
        # Save report
        report_file = self.base_dir / "experiments" / "statistical" / "statistical_analysis.json"
        with open(report_file, 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"📋 Statistical report saved to {report_file}")
        return report
    
    def plot_byzantine_tolerance(self):
        """Create visualization of Byzantine fault tolerance"""
        print("📈 Creating Byzantine Tolerance Visualization...")
        
        byzantine_analysis = self.analyze_byzantine_tolerance()
        
        if not byzantine_analysis:
            print("  No data to visualize")
            return
        
        # Prepare data for plotting
        node_counts = sorted(set(key[0] for key in byzantine_analysis.keys()))
        byzantine_ratios = sorted(set(key[1] for key in byzantine_analysis.keys()))
        
        # Create heatmap data
        heatmap_data = np.zeros((len(node_counts), len(byzantine_ratios)))
        
        for i, node_count in enumerate(node_counts):
            for j, byzantine_ratio in enumerate(byzantine_ratios):
                key = (node_count, byzantine_ratio, 0)  # Assume no crashed nodes for simplicity
                if key in byzantine_analysis:
                    heatmap_data[i, j] = byzantine_analysis[key]['success_rate']
        
        # Create heatmap
        plt.figure(figsize=(12, 8))
        im = plt.imshow(heatmap_data, cmap='RdYlGn', aspect='auto', vmin=0, vmax=100)
        
        plt.colorbar(im, label='Success Rate (%)')
        plt.xlabel('Byzantine Ratio (%)')
        plt.ylabel('Node Count')
        plt.title('Alpenglow Byzantine Fault Tolerance')
        
        plt.xticks(range(len(byzantine_ratios)), byzantine_ratios)
        plt.yticks(range(len(node_counts)), node_counts)
        
        # Add text annotations
        for i in range(len(node_counts)):
            for j in range(len(byzantine_ratios)):
                text = plt.text(j, i, f'{heatmap_data[i, j]:.0f}%',
                               ha="center", va="center", color="black")
        
        plt.tight_layout()
        
        # Save plot
        plots_dir = self.base_dir / "experiments" / "statistical" / "plots"
        plots_dir.mkdir(exist_ok=True)
        plt.savefig(plots_dir / "byzantine_tolerance_heatmap.png", dpi=300)
        plt.close()
        
        print(f"📊 Plot saved to {plots_dir}")

def main():
    """Run statistical analysis"""
    print("📊 Starting Alpenglow Statistical Analysis")
    print("=" * 50)
    
    analyzer = StatisticalAnalyzer()
    
    # Define test parameters
    node_counts = [10, 20, 30]
    byzantine_ratios = [5, 10, 15, 20]  # Percentage
    crashed_ratios = [0, 5, 10]  # Percentage
    num_samples = 20  # Reduced for demo
    
    # Run Monte Carlo simulation
    results = analyzer.monte_carlo_simulation(
        node_counts, byzantine_ratios, crashed_ratios, num_samples
    )
    
    # Generate analysis
    report = analyzer.generate_statistical_report()
    analyzer.plot_byzantine_tolerance()
    
    # Print summary
    print("\n📊 STATISTICAL ANALYSIS SUMMARY")
    print("=" * 40)
    print(f"Total Simulations: {report['summary']['total_simulations']}")
    print(f"Success Rate: {report['summary']['success_rate']:.1f}%")
    print(f"Avg States Explored: {report['summary']['avg_states_explored']:.0f}")
    print(f"Avg Runtime: {report['summary']['avg_runtime_seconds']:.1f}s")
    
    print("\n✅ Statistical Analysis Complete!")

if __name__ == "__main__":
    main()
