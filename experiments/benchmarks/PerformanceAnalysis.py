#!/usr/bin/env python3
"""
Alpenglow Consensus Performance Analysis
Benchmarking TLA+ model checking performance and scalability analysis
"""

import subprocess
import time
import json
import matplotlib.pyplot as plt
import pandas as pd
from pathlib import Path
import re

class AlpenglowBenchmark:
    def __init__(self):
        self.results = []
        self.base_dir = Path(__file__).parent.parent.parent
        self.tla_tools = self.base_dir / "tla2tools.jar"
        
    def run_tlc_benchmark(self, spec_file, config_file, timeout=300):
        """Run TLC model checker and collect performance metrics"""
        start_time = time.time()
        
        cmd = [
            "java", "-cp", str(self.tla_tools),
            "tlc2.TLC", "-config", str(config_file), str(spec_file)
        ]
        
        try:
            result = subprocess.run(
                cmd, 
                timeout=timeout,
                capture_output=True,
                text=True
            )
            
            end_time = time.time()
            runtime = end_time - start_time
            
            # Parse TLC output for metrics
            metrics = self.parse_tlc_output(result.stdout, result.stderr)
            metrics.update({
                'spec_file': spec_file.name,
                'config_file': config_file.name,
                'runtime_seconds': runtime,
                'exit_code': result.returncode,
                'timeout': False
            })
            
            return metrics
            
        except subprocess.TimeoutExpired:
            return {
                'spec_file': spec_file.name,
                'config_file': config_file.name,
                'runtime_seconds': timeout,
                'exit_code': -1,
                'timeout': True,
                'states_generated': 0,
                'distinct_states': 0,
                'states_per_second': 0
            }
    
    def parse_tlc_output(self, stdout, stderr):
        """Extract performance metrics from TLC output"""
        metrics = {
            'states_generated': 0,
            'distinct_states': 0,
            'states_per_second': 0,
            'memory_usage': 0,
            'invariant_violations': 0,
            'deadlocks': 0
        }
        
        # Parse state statistics
        state_pattern = r'(\d+) states generated.*?(\d+) distinct states'
        match = re.search(state_pattern, stdout)
        if match:
            metrics['states_generated'] = int(match.group(1))
            metrics['distinct_states'] = int(match.group(2))
            
        # Parse throughput
        throughput_pattern = r'\((\d+) s/min\)'
        match = re.search(throughput_pattern, stdout)
        if match:
            metrics['states_per_second'] = int(match.group(1)) / 60
            
        # Check for violations
        if 'Invariant' in stdout and 'violated' in stdout:
            metrics['invariant_violations'] = 1
            
        if 'Deadlock' in stdout:
            metrics['deadlocks'] = 1
            
        return metrics
    
    def benchmark_small_configs(self):
        """Benchmark small configuration model checking"""
        print("🔬 Benchmarking Small Configuration Model Checking...")
        
        small_config_dir = self.base_dir / "model-checking" / "small-config"
        
        configs = [
            ("MinimalAlpenglow.tla", "MinimalAlpenglow.cfg"),
            ("AlpenglowConsensus.tla", "AlpenglowConsensus.cfg"),
        ]
        
        for spec_name, config_name in configs:
            spec_file = small_config_dir / spec_name
            config_file = small_config_dir / config_name
            
            if spec_file.exists() and config_file.exists():
                print(f"  Running {spec_name}...")
                metrics = self.run_tlc_benchmark(spec_file, config_file, timeout=120)
                self.results.append(metrics)
                
                print(f"    States: {metrics['distinct_states']:,}")
                print(f"    Runtime: {metrics['runtime_seconds']:.1f}s")
                print(f"    Throughput: {metrics['states_per_second']:.0f} states/sec")
                
    def benchmark_scalability(self):
        """Analyze scalability with different parameters"""
        print("📈 Analyzing Scalability...")
        
        # Create configurations with different node counts
        scalability_results = []
        
        for nodes in [3, 4, 5, 6]:
            print(f"  Testing {nodes} nodes...")
            
            # Generate dynamic configuration
            config_metrics = self.estimate_state_space(nodes)
            scalability_results.append({
                'nodes': nodes,
                'estimated_states': config_metrics['estimated_states'],
                'theoretical_runtime': config_metrics['theoretical_runtime']
            })
            
        return scalability_results
    
    def estimate_state_space(self, nodes):
        """Estimate state space complexity for given parameters"""
        slots = 3
        hashes = 2
        vote_types = 2
        
        # Rough estimation based on combinatorics
        max_votes_per_slot = nodes * hashes * vote_types
        vote_combinations = 2 ** max_votes_per_slot
        finalization_states = 2 ** (slots * hashes)
        
        estimated_states = vote_combinations * finalization_states
        
        # Estimate runtime based on observed throughput
        avg_throughput = 5000  # states per second
        theoretical_runtime = estimated_states / avg_throughput
        
        return {
            'estimated_states': estimated_states,
            'theoretical_runtime': theoretical_runtime
        }
    
    def analyze_memory_usage(self):
        """Analyze memory usage patterns"""
        print("💾 Analyzing Memory Usage...")
        
        # Extract memory usage from results
        memory_data = []
        for result in self.results:
            if not result['timeout']:
                memory_data.append({
                    'spec': result['spec_file'],
                    'states': result['distinct_states'],
                    'memory_per_state': result.get('memory_usage', 0) / max(result['distinct_states'], 1)
                })
        
        return memory_data
    
    def generate_report(self):
        """Generate comprehensive performance report"""
        print("📊 Generating Performance Report...")
        
        df = pd.DataFrame(self.results)
        
        report = {
            'summary': {
                'total_specs_tested': len(self.results),
                'total_states_explored': df['distinct_states'].sum(),
                'total_runtime': df['runtime_seconds'].sum(),
                'average_throughput': df['states_per_second'].mean(),
                'success_rate': (df['exit_code'] == 0).mean() * 100
            },
            'detailed_results': self.results,
            'scalability_analysis': self.benchmark_scalability(),
            'memory_analysis': self.analyze_memory_usage()
        }
        
        # Save report
        report_file = self.base_dir / "experiments" / "benchmarks" / "performance_report.json"
        with open(report_file, 'w') as f:
            json.dump(report, f, indent=2)
            
        print(f"📋 Report saved to {report_file}")
        return report
    
    def plot_results(self):
        """Generate performance visualization plots"""
        print("📈 Generating Performance Plots...")
        
        if not self.results:
            return
            
        # Create plots directory
        plots_dir = self.base_dir / "experiments" / "benchmarks" / "plots"
        plots_dir.mkdir(exist_ok=True)
        
        # Plot 1: States vs Runtime
        plt.figure(figsize=(10, 6))
        
        specs = [r['spec_file'] for r in self.results]
        states = [r['distinct_states'] for r in self.results]
        runtimes = [r['runtime_seconds'] for r in self.results]
        
        plt.scatter(states, runtimes, s=100, alpha=0.7)
        for i, spec in enumerate(specs):
            plt.annotate(spec, (states[i], runtimes[i]), 
                        xytext=(5, 5), textcoords='offset points')
        
        plt.xlabel('Distinct States Explored')
        plt.ylabel('Runtime (seconds)')
        plt.title('Alpenglow Model Checking Performance')
        plt.grid(True, alpha=0.3)
        plt.tight_layout()
        plt.savefig(plots_dir / "states_vs_runtime.png", dpi=300)
        plt.close()
        
        # Plot 2: Throughput comparison
        plt.figure(figsize=(10, 6))
        
        throughputs = [r['states_per_second'] for r in self.results if r['states_per_second'] > 0]
        spec_names = [r['spec_file'] for r in self.results if r['states_per_second'] > 0]
        
        plt.bar(range(len(throughputs)), throughputs)
        plt.xlabel('Specification')
        plt.ylabel('Throughput (states/second)')
        plt.title('Model Checking Throughput by Specification')
        plt.xticks(range(len(spec_names)), spec_names, rotation=45)
        plt.tight_layout()
        plt.savefig(plots_dir / "throughput_comparison.png", dpi=300)
        plt.close()
        
        print(f"📊 Plots saved to {plots_dir}")

def main():
    """Run complete benchmark suite"""
    print("🚀 Starting Alpenglow Consensus Performance Benchmark")
    print("=" * 60)
    
    benchmark = AlpenglowBenchmark()
    
    # Run benchmarks
    benchmark.benchmark_small_configs()
    
    # Generate analysis
    report = benchmark.generate_report()
    benchmark.plot_results()
    
    # Print summary
    print("\n📊 BENCHMARK SUMMARY")
    print("=" * 40)
    print(f"Specs Tested: {report['summary']['total_specs_tested']}")
    print(f"Total States: {report['summary']['total_states_explored']:,}")
    print(f"Total Runtime: {report['summary']['total_runtime']:.1f}s")
    print(f"Avg Throughput: {report['summary']['average_throughput']:.0f} states/sec")
    print(f"Success Rate: {report['summary']['success_rate']:.1f}%")
    
    print("\n✅ Benchmark Complete!")

if __name__ == "__main__":
    main()
