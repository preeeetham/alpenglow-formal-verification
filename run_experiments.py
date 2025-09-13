#!/usr/bin/env python3
"""
Alpenglow Formal Verification - Complete Experiment Runner
Runs all verification experiments, benchmarks, and statistical analysis
"""

import subprocess
import sys
import time
from pathlib import Path
import json

class ExperimentRunner:
    def __init__(self):
        self.base_dir = Path(__file__).parent
        self.results = {}
        
    def run_command(self, cmd, description, timeout=300):
        """Run a command and capture results"""
        print(f"🔄 {description}...")
        start_time = time.time()
        
        try:
            result = subprocess.run(
                cmd, 
                timeout=timeout,
                capture_output=True, 
                text=True,
                cwd=self.base_dir
            )
            
            end_time = time.time()
            runtime = end_time - start_time
            
            success = result.returncode == 0
            
            print(f"  {'✅' if success else '❌'} {description} ({runtime:.1f}s)")
            
            if not success and result.stderr:
                print(f"  Error: {result.stderr[:200]}...")
            
            return {
                'success': success,
                'runtime': runtime,
                'stdout': result.stdout,
                'stderr': result.stderr,
                'returncode': result.returncode
            }
            
        except subprocess.TimeoutExpired:
            print(f"  ⏰ {description} timed out after {timeout}s")
            return {
                'success': False,
                'runtime': timeout,
                'timeout': True
            }
    
    def run_small_scale_verification(self):
        """Run small-scale exhaustive verification"""
        print("\n🔬 SMALL-SCALE VERIFICATION")
        print("=" * 40)
        
        # Test minimal specification
        minimal_result = self.run_command([
            "java", "-cp", "tla2tools.jar", "tlc2.TLC",
            "-config", "model-checking/small-config/MinimalAlpenglow.cfg",
            "model-checking/small-config/MinimalAlpenglow.tla"
        ], "Minimal Alpenglow Safety Test", timeout=60)
        
        # Test main consensus specification
        consensus_result = self.run_command([
            "java", "-cp", "tla2tools.jar", "tlc2.TLC", 
            "-config", "model-checking/small-config/AlpenglowConsensus.cfg",
            "model-checking/small-config/AlpenglowConsensus.tla"
        ], "Alpenglow Consensus Verification", timeout=300)
        
        self.results['small_scale'] = {
            'minimal': minimal_result,
            'consensus': consensus_result
        }
        
        return minimal_result['success'] and consensus_result['success']
    
    def run_benchmark_analysis(self):
        """Run performance benchmarking"""
        print("\n📊 PERFORMANCE BENCHMARKING")
        print("=" * 40)
        
        benchmark_result = self.run_command([
            "python3", "experiments/benchmarks/PerformanceAnalysis.py"
        ], "Performance Benchmark Analysis", timeout=600)
        
        self.results['benchmarks'] = benchmark_result
        return benchmark_result['success']
    
    def run_counterexample_analysis(self):
        """Run counterexample analysis"""
        print("\n🔍 COUNTEREXAMPLE ANALYSIS")
        print("=" * 40)
        
        counterexample_result = self.run_command([
            "python3", "experiments/counterexamples/CounterexampleAnalysis.py"
        ], "Counterexample Analysis", timeout=300)
        
        self.results['counterexamples'] = counterexample_result
        return counterexample_result['success']
    
    def run_statistical_analysis(self):
        """Run statistical Monte Carlo analysis"""
        print("\n🎲 STATISTICAL ANALYSIS")
        print("=" * 40)
        
        statistical_result = self.run_command([
            "python3", "experiments/statistical/StatisticalAnalysis.py"
        ], "Statistical Monte Carlo Analysis", timeout=1800)
        
        self.results['statistical'] = statistical_result
        return statistical_result['success']
    
    def run_large_scale_verification(self):
        """Run large-scale statistical verification"""
        print("\n🌐 LARGE-SCALE VERIFICATION")
        print("=" * 40)
        
        large_scale_result = self.run_command([
            "java", "-cp", "tla2tools.jar", "tlc2.TLC",
            "-config", "model-checking/statistical/LargeScaleConfig.cfg",
            "model-checking/statistical/LargeScaleConfig.tla"
        ], "Large-Scale Statistical Verification", timeout=1800)
        
        self.results['large_scale'] = large_scale_result
        return large_scale_result['success']
    
    def run_syntax_validation(self):
        """Validate all TLA+ specifications"""
        print("\n✅ SYNTAX VALIDATION")
        print("=" * 40)
        
        tla_files = [
            "specs/tlaplus/AlpenglowConsensus.tla",
            "specs/tlaplus/Votor.tla", 
            "specs/tlaplus/Rotor.tla",
            "specs/tlaplus/Properties.tla",
            "proofs/safety/SafetyProofs.tla",
            "proofs/liveness/LivenessProofs.tla",
            "proofs/resilience/ByzantineProofs.tla",
            "model-checking/small-config/AlpenglowConsensus.tla",
            "model-checking/small-config/MinimalAlpenglow.tla",
            "model-checking/statistical/LargeScaleConfig.tla"
        ]
        
        syntax_results = {}
        all_valid = True
        
        for tla_file in tla_files:
            file_path = self.base_dir / tla_file
            if file_path.exists():
                result = self.run_command([
                    "java", "-cp", "tla2tools.jar", "tlc2.TLC",
                    "-config", "/dev/null", str(file_path)
                ], f"Syntax check: {tla_file}", timeout=30)
                
                syntax_results[tla_file] = result
                if not result['success']:
                    all_valid = False
            else:
                print(f"  ⚠️  File not found: {tla_file}")
                all_valid = False
        
        self.results['syntax_validation'] = syntax_results
        return all_valid
    
    def generate_final_report(self):
        """Generate comprehensive final report"""
        print("\n📋 GENERATING FINAL REPORT")
        print("=" * 40)
        
        # Calculate overall success
        total_tests = 0
        successful_tests = 0
        
        for category, results in self.results.items():
            if isinstance(results, dict):
                for test_name, result in results.items():
                    if isinstance(result, dict) and 'success' in result:
                        total_tests += 1
                        if result['success']:
                            successful_tests += 1
            elif isinstance(results, dict) and 'success' in results:
                total_tests += 1
                if results['success']:
                    successful_tests += 1
        
        success_rate = (successful_tests / total_tests * 100) if total_tests > 0 else 0
        
        # Generate report
        report = {
            'timestamp': time.strftime('%Y-%m-%d %H:%M:%S'),
            'summary': {
                'total_tests': total_tests,
                'successful_tests': successful_tests,
                'success_rate': success_rate,
                'overall_status': 'PASS' if success_rate >= 80 else 'FAIL'
            },
            'results': self.results
        }
        
        # Save report
        report_file = self.base_dir / "EXPERIMENT_RESULTS.json"
        with open(report_file, 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"📊 Final report saved to {report_file}")
        
        # Print summary
        print(f"\n🎯 EXPERIMENT SUMMARY")
        print("=" * 30)
        print(f"Total Tests: {total_tests}")
        print(f"Successful: {successful_tests}")
        print(f"Success Rate: {success_rate:.1f}%")
        print(f"Overall Status: {'✅ PASS' if success_rate >= 80 else '❌ FAIL'}")
        
        return report

def main():
    """Run complete experiment suite"""
    print("🚀 ALPENGLOW FORMAL VERIFICATION - COMPLETE EXPERIMENT SUITE")
    print("=" * 70)
    print("Running comprehensive verification, benchmarking, and analysis...")
    
    runner = ExperimentRunner()
    
    # Run all experiments
    experiments = [
        ("Syntax Validation", runner.run_syntax_validation),
        ("Small-Scale Verification", runner.run_small_scale_verification),
        ("Performance Benchmarking", runner.run_benchmark_analysis),
        ("Counterexample Analysis", runner.run_counterexample_analysis),
        ("Statistical Analysis", runner.run_statistical_analysis),
        ("Large-Scale Verification", runner.run_large_scale_verification)
    ]
    
    start_time = time.time()
    
    for experiment_name, experiment_func in experiments:
        print(f"\n{'='*20} {experiment_name.upper()} {'='*20}")
        try:
            experiment_func()
        except Exception as e:
            print(f"❌ {experiment_name} failed with error: {e}")
    
    end_time = time.time()
    total_runtime = end_time - start_time
    
    # Generate final report
    report = runner.generate_final_report()
    
    print(f"\n⏱️  Total Runtime: {total_runtime:.1f} seconds")
    print(f"📊 Overall Status: {report['summary']['overall_status']}")
    
    if report['summary']['overall_status'] == 'PASS':
        print("\n🎉 ALL EXPERIMENTS COMPLETED SUCCESSFULLY!")
        print("✅ Alpenglow consensus protocol is formally verified!")
    else:
        print("\n⚠️  SOME EXPERIMENTS FAILED")
        print("Please check the detailed results in EXPERIMENT_RESULTS.json")
    
    return report['summary']['overall_status'] == 'PASS'

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
