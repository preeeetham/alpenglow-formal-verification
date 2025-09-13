#!/usr/bin/env python3
"""
Alpenglow Consensus Counterexample Analysis
Analyze and visualize counterexamples from model checking failures
"""

import subprocess
import re
import json
from pathlib import Path
import matplotlib.pyplot as plt
import networkx as nx

class CounterexampleAnalyzer:
    def __init__(self):
        self.base_dir = Path(__file__).parent.parent.parent
        self.tla_tools = self.base_dir / "tla2tools.jar"
        self.counterexamples = []
        
    def generate_counterexample(self, spec_file, config_file, property_name):
        """Generate counterexample for a specific property violation"""
        print(f"🔍 Generating counterexample for {property_name}...")
        
        # Create a modified config that will likely fail
        failing_config = self.create_failing_config(config_file, property_name)
        
        cmd = [
            "java", "-cp", str(self.tla_tools),
            "tlc2.TLC", "-config", str(failing_config), str(spec_file)
        ]
        
        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
            
            if "Error:" in result.stdout or "violated" in result.stdout:
                counterexample = self.parse_counterexample(result.stdout, property_name)
                self.counterexamples.append(counterexample)
                return counterexample
            else:
                print(f"  No counterexample found for {property_name}")
                return None
                
        except subprocess.TimeoutExpired:
            print(f"  Timeout generating counterexample for {property_name}")
            return None
    
    def create_failing_config(self, config_file, property_name):
        """Create a configuration that will likely violate the property"""
        failing_config = self.base_dir / "experiments" / "counterexamples" / f"failing_{property_name}.cfg"
        failing_config.parent.mkdir(exist_ok=True)
        
        # Read original config
        with open(config_file, 'r') as f:
            content = f.read()
        
        # Modify to create failure conditions
        if property_name == "Safety":
            # Add conflicting vote scenarios
            content += "\n\n(* Force conflicting finalizations *)\n"
            content += "CONSTANTS\n    ForceConflict = TRUE\n"
        elif property_name == "TypeOK":
            # Add invalid type scenarios
            content += "\n\n(* Force type violations *)\n"
            content += "CONSTANTS\n    ForceTypeError = TRUE\n"
        
        with open(failing_config, 'w') as f:
            f.write(content)
            
        return failing_config
    
    def parse_counterexample(self, output, property_name):
        """Parse counterexample from TLC output"""
        counterexample = {
            'property': property_name,
            'states': [],
            'violation_state': None,
            'trace_length': 0,
            'error_message': ""
        }
        
        # Extract state trace
        state_pattern = r'State (\d+):.*?<(.+?)>'
        states = re.findall(state_pattern, output, re.DOTALL)
        
        for state_num, state_content in states:
            state = self.parse_state(state_content)
            counterexample['states'].append({
                'number': int(state_num),
                'content': state
            })
        
        counterexample['trace_length'] = len(states)
        
        # Find violation state
        if "violated" in output:
            violation_match = re.search(r'State (\d+).*?violated', output)
            if violation_match:
                counterexample['violation_state'] = int(violation_match.group(1))
        
        # Extract error message
        error_match = re.search(r'Error: (.+?)(?:\n|$)', output)
        if error_match:
            counterexample['error_message'] = error_match.group(1)
        
        return counterexample
    
    def parse_state(self, state_content):
        """Parse individual state content"""
        state = {}
        
        # Extract variable assignments
        var_pattern = r'(\w+)\s*=\s*([^\n]+)'
        matches = re.findall(var_pattern, state_content)
        
        for var_name, var_value in matches:
            state[var_name] = var_value.strip()
        
        return state
    
    def analyze_safety_violations(self):
        """Analyze safety property violations"""
        print("🔒 Analyzing Safety Violations...")
        
        safety_violations = [ce for ce in self.counterexamples if ce['property'] == 'Safety']
        
        if not safety_violations:
            print("  No safety violations found")
            return
        
        analysis = {
            'total_violations': len(safety_violations),
            'common_patterns': [],
            'violation_causes': []
        }
        
        for violation in safety_violations:
            # Analyze the violation pattern
            if violation['violation_state']:
                violation_state = violation['states'][violation['violation_state'] - 1]
                
                # Check for conflicting finalizations
                if 'finalized' in violation_state['content']:
                    finalized_content = violation_state['content']['finalized']
                    if 'A' in finalized_content and 'B' in finalized_content:
                        analysis['violation_causes'].append('Conflicting block finalization')
        
        return analysis
    
    def visualize_trace(self, counterexample):
        """Visualize counterexample trace as a state graph"""
        if not counterexample['states']:
            return
        
        G = nx.DiGraph()
        
        # Add states as nodes
        for state in counterexample['states']:
            state_id = f"S{state['number']}"
            G.add_node(state_id, **state['content'])
        
        # Add transitions as edges
        for i in range(len(counterexample['states']) - 1):
            current = f"S{counterexample['states'][i]['number']}"
            next_state = f"S{counterexample['states'][i+1]['number']}"
            G.add_edge(current, next_state)
        
        # Highlight violation state
        if counterexample['violation_state']:
            violation_node = f"S{counterexample['violation_state']}"
            if violation_node in G.nodes():
                G.nodes[violation_node]['violation'] = True
        
        return G
    
    def generate_counterexample_report(self):
        """Generate comprehensive counterexample analysis report"""
        print("📋 Generating Counterexample Analysis Report...")
        
        report = {
            'summary': {
                'total_counterexamples': len(self.counterexamples),
                'properties_tested': list(set(ce['property'] for ce in self.counterexamples)),
                'average_trace_length': sum(ce['trace_length'] for ce in self.counterexamples) / len(self.counterexamples) if self.counterexamples else 0
            },
            'counterexamples': self.counterexamples,
            'safety_analysis': self.analyze_safety_violations()
        }
        
        # Save report
        report_file = self.base_dir / "experiments" / "counterexamples" / "counterexample_analysis.json"
        with open(report_file, 'w') as f:
            json.dump(report, f, indent=2)
        
        print(f"📊 Counterexample report saved to {report_file}")
        return report
    
    def create_failing_specifications(self):
        """Create intentionally failing specifications for testing"""
        print("🧪 Creating Failing Specifications for Testing...")
        
        failing_specs_dir = self.base_dir / "experiments" / "counterexamples" / "failing_specs"
        failing_specs_dir.mkdir(exist_ok=True)
        
        # 1. Safety violation spec
        safety_violation_spec = """
---- MODULE SafetyViolation ----
EXTENDS Naturals, FiniteSets

VARIABLES finalized

Init == finalized = {}

(* Intentionally broken: allows conflicting finalizations *)
FinalizeBlock(slot, hash) ==
    finalized' = finalized \\union {<<slot, hash>>}

Next ==
    \\E slot \\in {1, 2}, hash \\in {"A", "B"} :
        FinalizeBlock(slot, hash)

Spec == Init /\\ [][Next]_finalized

(* This will be violated *)
Safety ==
    \\A b1, b2 \\in finalized :
        b1[1] = b2[1] => b1[2] = b2[2]

====
"""
        
        with open(failing_specs_dir / "SafetyViolation.tla", 'w') as f:
            f.write(safety_violation_spec)
        
        # 2. Type violation spec
        type_violation_spec = """
---- MODULE TypeViolation ----
EXTENDS Naturals

VARIABLES x

Init == x = 0

(* Intentionally broken: assigns string to numeric variable *)
Next == x' = "invalid"

Spec == Init /\\ [][Next]_x

====
"""
        
        with open(failing_specs_dir / "TypeViolation.tla", 'w') as f:
            f.write(type_violation_spec)
        
        print(f"  Created failing specifications in {failing_specs_dir}")
    
    def run_counterexample_tests(self):
        """Run counterexample generation tests"""
        print("🧪 Running Counterexample Tests...")
        
        # Create failing specs
        self.create_failing_specifications()
        
        # Test safety violation
        safety_spec = self.base_dir / "experiments" / "counterexamples" / "failing_specs" / "SafetyViolation.tla"
        safety_config = self.base_dir / "experiments" / "counterexamples" / "failing_specs" / "SafetyViolation.cfg"
        
        # Create config for safety violation
        safety_config_content = """
SPECIFICATION Spec

INVARIANTS
    Safety
"""
        
        with open(safety_config, 'w') as f:
            f.write(safety_config_content)
        
        # Generate counterexample
        self.generate_counterexample(safety_spec, safety_config, "Safety")

def main():
    """Run counterexample analysis"""
    print("🔍 Starting Alpenglow Counterexample Analysis")
    print("=" * 50)
    
    analyzer = CounterexampleAnalyzer()
    
    # Run tests
    analyzer.run_counterexample_tests()
    
    # Generate analysis
    report = analyzer.generate_counterexample_report()
    
    # Print summary
    print("\n📊 COUNTEREXAMPLE ANALYSIS SUMMARY")
    print("=" * 40)
    print(f"Counterexamples Found: {report['summary']['total_counterexamples']}")
    print(f"Properties Tested: {', '.join(report['summary']['properties_tested'])}")
    print(f"Avg Trace Length: {report['summary']['average_trace_length']:.1f}")
    
    print("\n✅ Counterexample Analysis Complete!")

if __name__ == "__main__":
    main()
