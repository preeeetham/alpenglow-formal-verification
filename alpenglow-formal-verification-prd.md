# Alpenglow Formal Verification - Product Requirements Document

## Project Overview

**Project Name**: Formal Verification of Solana Alpenglow Consensus Protocol  
**Framework**: TLA+ or Stateright (Rust-based model checker)  
**Objective**: Transform mathematical theorems from Alpenglow whitepaper into machine-checkable formal proofs  
**License**: Apache 2.0 (Open Source)

### Executive Summary

Alpenglow is Solana's next-generation consensus protocol providing:
- **100-150ms finalization** (100x faster than current TowerBFT)
- **Dual-path consensus**: Votor enables fast finalization with 80% stake or conservative with 60% stake
- **Optimized block propagation**: Rotor uses erasure coding for efficient single-hop block distribution  
- **"20+20" resilience**: Tolerates up to 20% Byzantine nodes + 20% crashed/offline nodes

The challenge is to create machine-verifiable proofs for all safety, liveness, and resilience properties claimed in the academic whitepaper.

---

## Key Technical Components

### 1. Alpenglow Protocol Architecture

#### 1.1 Votor (Voting Component)
- **Fast Path**: Single round finalization with ≥80% stake participation
- **Slow Path**: Two round finalization with ≥60% stake participation
- **Concurrent execution**: Both paths run simultaneously, finalization occurs at min(δ₈₀%, 2δ₆₀%)

#### 1.2 Rotor (Block Distribution Component)
- **Erasure coding**: Reed-Solomon (Γ, γ) codes with data expansion ratio κ = Γ/γ
- **Stake-weighted relay sampling**: Novel committee sampling (PS-P) for improved resilience
- **Merkle trees**: Authentication of shred fragments
- **UDP-based**: Messages fit within 1,500 byte limit

#### 1.3 Core Data Structures
- **Shreds**: Erasure-coded fragments fitting in UDP datagrams
- **Slices**: Collections of shreds that can be decoded with γ out of Γ fragments  
- **Blocks**: Sequences of slices with Merkle tree commitment
- **Certificates**: Aggregated signatures for different vote types

### 1.4 Vote Types and Certificates
```
Vote Types:
- NotarVote(slot, hash): Basic block approval
- NotarFallbackVote(slot, hash): Fallback approval after SafeToNotar
- SkipVote(slot): Vote to skip a slot
- SkipFallbackVote(slot): Fallback skip after SafeToSkip  
- FinalVote(slot): Final confirmation vote

Certificate Types:
- Fast-Finalization: ≥80% NotarVote
- Notarization: ≥60% NotarVote
- Notar-Fallback: ≥60% (NotarVote OR NotarFallbackVote)
- Skip: ≥60% (SkipVote OR SkipFallbackVote)
- Finalization: ≥60% FinalVote
```

---

## Formal Methods Framework Selection

### Option 1: TLA+ (Recommended for Academic Rigor)

**Pros:**
- Industry standard for distributed systems verification (AWS, Microsoft, etc.)
- Rich temporal logic expressiveness (LTL/CTL)
- Mature toolchain (TLC model checker, TLAPS theorem prover)
- Strong academic validation
- Extensive examples in consensus protocols

**Cons:**  
- Learning curve for implementation
- Abstract modeling requires careful refinement to implementation

**Key Tools:**
- **TLA+**: Specification language
- **TLC**: Model checker for finite state verification
- **TLAPS**: Theorem prover for infinite state proofs
- **PlusCal**: Algorithm description language (optional)

### Option 2: Stateright (Alternative for Implementation Fidelity)

**Pros:**
- Direct Rust implementation verification
- No abstraction gap between model and code
- Embedded model checker in same language as Solana
- Modern tooling and visualization

**Cons:**
- Newer framework with smaller community
- Limited to finite state model checking
- Less academic precedent for consensus verification

**Key Tools:**
- **stateright**: Rust library for actor-based model checking
- **Actor trait**: For modeling distributed components
- **Model trait**: For state space exploration

---

## Technical Requirements

### 1. Complete Formal Specification

#### 1.1 Core Protocol Components
```tla+
(* TLA+ specification structure *)
MODULE AlpenglowConsensus

VARIABLES 
  nodes,           \* Set of validator nodes
  stake,           \* Stake distribution  
  slots,           \* Time slots
  leaders,         \* Leader schedule
  blocks,          \* Proposed blocks
  votes,           \* Vote pool
  certificates,    \* Certificate store
  network          \* Network model

Init == (* Initial state *)
Next == (* State transitions *)
Spec == Init /\ [][Next]_vars
```

#### 1.2 Votor Specification Requirements
- Dual voting paths (80% fast, 60% slow)
- Vote generation logic with timeout handling
- Certificate aggregation and validation  
- SafeToNotar/SafeToSkip event triggers
- Leader window management

#### 1.3 Rotor Specification Requirements
- Erasure coding encode/decode operations
- Stake-weighted relay sampling (PS-P algorithm)
- Merkle tree construction and validation
- UDP message constraints (≤1,500 bytes)
- Network delay models (δ, ∆ parameters)

### 2. Machine-Verified Theorems

#### 2.1 Safety Properties
```tla+
(* No conflicting blocks finalized *)
Safety == [](\A s \in Slots : 
  \A b1, b2 \in FinalizedBlocks : 
    (slot(b1) = s /\ slot(b2) = s) => b1 = b2)

(* Chain consistency *)
ChainConsistency == [](\A b1, b2 \in FinalizedBlocks :
  slot(b1) <= slot(b2) => b2 DescendantOf b1)

(* Certificate uniqueness *)
CertificateUniqueness == [](\A cert1, cert2 \in Certificates :
  (type(cert1) = type(cert2) /\ slot(cert1) = slot(cert2)) 
  => cert1 = cert2)
```

#### 2.2 Liveness Properties
```tla+
(* Progress under partial synchrony *)
Progress == (\A s \in Slots : HonestStake > 60%) => 
  <>(\E b \in Blocks : Finalized(b))

(* Fast path completion *)
FastPath == (ResponsiveStake > 80%) => 
  <>(\E b \in Blocks : FastFinalized(b))

(* Bounded finalization time *)
BoundedFinalization == [](\A b \in ProposedBlocks :
  FinalizationTime(b) <= Min(Delta80Percent, 2 * Delta60Percent))
```

#### 2.3 Resilience Properties  
```tla+
(* Byzantine fault tolerance *)
ByzantineSafety == (ByzantineStake < 20%) => []Safety

(* Crash fault tolerance *)
CrashLiveness == (ByzantineStake < 20% /\ CrashedStake < 20%) =>
  <>Progress

(* Network partition recovery *)
PartitionRecovery == (NetworkPartitioned /\ <>NetworkHealed) =>
  <>Progress
```

### 3. Model Checking & Validation

#### 3.1 Small Configuration Verification
- **Exhaustive verification**: 4-10 nodes
- **State space exploration**: All possible message interleavings
- **Invariant checking**: Safety properties on all reachable states
- **Counterexample generation**: Bug reproduction traces

#### 3.2 Realistic Scale Validation  
- **Statistical model checking**: Large node sets (100-1500 nodes)
- **Monte Carlo simulation**: Random behavior sampling
- **Performance analysis**: Latency/throughput measurements
- **Parameter sensitivity**: Varying κ, γ, Γ, ∆ values

---

## Mathematical Formulas and Parameters

### Key Protocol Parameters
```
w = 4           # Blocks per leader window
γ = 32          # Data shreds per slice  
Γ = 64          # Total shreds per slice (including coding)
κ = Γ/γ = 2     # Data expansion ratio
nmax = 2000     # Maximum nodes
∆block = 400ms  # Block time
∆timeout = 1∆+2∆ # Timeout parameter  
∆standstill = 10s # Standstill trigger
ε = 5%          # Timeout increase rate
```

### Network Delay Models
```
δ = actual network delay (variable, unknown)
∆ = maximum network delay bound (protocol parameter)
δθ = delay to reach fraction θ of stake
```

### Stake Distribution
```
ρi = stake fraction for node i
Σρi = 1 (total stake)
Byzantine stake < 20%
Crashed stake < 20% (under Assumption 2)
Honest stake > 60%
```

### Erasure Coding Mathematics
```
Reed-Solomon (Γ, γ) code:
- Encodes message M into Γ fragments
- Any γ fragments sufficient for reconstruction  
- Data expansion rate κ = Γ/γ
- Merkle tree root r commits to all fragments
```

### Finalization Time Formula
```
Finalization time = min(δ80%, 2δ60%)

Where:
δ80% = time for 80% stake to communicate
δ60% = time for 60% stake to communicate  
```

---

## Implementation Languages and Tools

### For TLA+ Approach
- **TLA+**: Specification language
- **PlusCal**: Optional algorithmic description
- **TLC**: Model checker (Java-based)
- **TLAPS**: Theorem prover  
- **VSCode TLA+ extension**: Development environment

### For Stateright Approach  
- **Rust**: Implementation language
- **stateright crate**: Model checking framework
- **tokio**: Async runtime (if needed)
- **serde**: Serialization for network messages
- **criterion**: Benchmarking framework

### Supporting Tools
- **Git**: Version control
- **GitHub Actions**: CI/CD pipeline
- **Docker**: Reproducible build environment
- **LaTeX**: Mathematical documentation
- **Graphviz**: State diagram visualization

---

## Deliverables Structure

### 1. GitHub Repository Structure
```
alpenglow-formal-verification/
├── README.md                    # Project overview
├── LICENSE                      # Apache 2.0 license
├── specs/                       # Formal specifications
│   ├── tlaplus/                # TLA+ specifications (if chosen)
│   │   ├── AlpenglowConsensus.tla
│   │   ├── Votor.tla
│   │   ├── Rotor.tla  
│   │   └── Properties.tla
│   └── stateright/             # Stateright specs (if chosen)
│       ├── src/
│       ├── Cargo.toml
│       └── tests/
├── proofs/                     # Verification results
│   ├── safety/
│   ├── liveness/
│   └── resilience/
├── model-checking/             # Model checking configs
│   ├── small-config/           # 4-10 nodes
│   └── statistical/            # Large-scale validation  
├── docs/                       # Documentation
│   ├── technical-report.pdf
│   └── video-walkthrough.mp4
└── experiments/               # Validation experiments
    ├── benchmarks/
    └── counterexamples/
```

### 2. Technical Report Content
- **Executive Summary**: High-level verification results
- **Methodology**: Formal methods approach chosen
- **Specification Overview**: Key model components
- **Verification Results**: Theorem-by-theorem status
- **Counterexamples**: Any discovered issues
- **Performance Analysis**: Model checking statistics
- **Lessons Learned**: Insights and recommendations

### 3. Video Walkthrough Requirements
- **Duration**: 15-30 minutes
- **Content**: Live demonstration of formal verification
- **Tools**: Screen recording of model checker execution
- **Explanation**: Technical commentary on proofs
- **Results**: Summary of verification outcomes

---

## Verification Strategy

### Phase 1: Core Safety Properties (Weeks 1-3)
1. Model basic Votor voting logic
2. Specify certificate generation rules
3. Prove no conflicting finalization
4. Verify chain consistency
5. Check certificate uniqueness

### Phase 2: Liveness Properties (Weeks 4-6)
1. Model network synchrony assumptions  
2. Specify timeout mechanisms
3. Prove progress under honest majority
4. Verify fast path completion
5. Check bounded finalization time

### Phase 3: Advanced Properties (Weeks 7-8)
1. Model Rotor erasure coding
2. Specify crash fault scenarios
3. Verify Byzantine resilience
4. Check network partition recovery
5. Validate parameter bounds

### Phase 4: Validation & Documentation (Weeks 9-10)
1. Exhaustive small-scale model checking
2. Statistical validation for realistic scales
3. Performance analysis and benchmarking
4. Technical report writing
5. Video demonstration creation

---

## Risk Assessment

### Technical Risks
- **Specification Complexity**: Alpenglow has intricate dual-path logic
- **State Space Explosion**: Large node counts may exceed model checker limits
- **Abstraction Gap**: Formal model may miss implementation details
- **Tool Limitations**: TLC/Stateright capacity constraints

### Mitigation Strategies
- **Incremental Development**: Start with simplified models
- **Symmetry Reduction**: Exploit node equivalence to reduce state space  
- **Compositional Verification**: Verify components separately
- **Multiple Approaches**: Try both TLA+ and Stateright if needed

### Success Criteria
- **Minimum Viable**: Core safety properties verified for small configurations
- **Target Goal**: Full specification with all properties verified
- **Stretch Goal**: Large-scale validation + performance analysis + discovered optimizations

---

## Resources and References

### Primary Sources
1. **Alpenglow Whitepaper v1.1** (115 pages) - Complete protocol specification
2. **Solana Documentation** - Current TowerBFT implementation details
3. **Academic Papers** - Consensus protocol formal verification examples

### Tool Documentation
1. **TLA+ Homepage**: https://lamport.azurewebsites.net/tla/tla.html
2. **Stateright Book**: https://www.stateright.rs/
3. **TLA+ Examples**: https://github.com/tlaplus/Examples
4. **Stateright Examples**: https://github.com/stateright/stateright

### Academic References
1. "Holistic Verification of Blockchain Consensus" (DISC 2022)
2. "Formal Analysis of CBC Casper Consensus Algorithm with TLA+" 
3. "Reusable Formal Verification of DAG-based Consensus Protocols"
4. "Building Distributed Systems With Stateright"

### Alpenglow-Specific Resources
1. Accelerate Alpenglow Presentation Slides
2. Alpenglow Reference Implementation  
3. "Scale or Die at Accelerate 2025" presentation
4. Solana consensus documentation

---

## Development Environment Setup

### TLA+ Environment
```bash
# Install TLA+ tools
wget https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
wget https://github.com/tlaplus/tlaplus/releases/latest/download/tlc2.jar

# Install VSCode extension
code --install-extension alygin.vscode-tlaplus

# Verify installation
java -jar tla2tools.jar
```

### Stateright Environment  
```bash
# Install Rust
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Create new project
cargo new alpenglow-verification --lib
cd alpenglow-verification

# Add dependencies to Cargo.toml
[dependencies]
stateright = "0.31"
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.0", features = ["full"] }
```

### Cursor IDE Configuration
```json
{
  "tlaplus.java.options": "-Xmx4g",
  "tlaplus.tlc.modelChecker.extraOptions": "-workers auto",
  "rust-analyzer.cargo.loadOutDirsFromCheck": true,
  "rust-analyzer.procMacro.enable": true
}
```

This comprehensive PRD provides all the technical details, mathematical formulas, implementation guidelines, and resources needed to successfully implement formal verification of the Alpenglow consensus protocol using Cursor IDE and either TLA+ or Stateright frameworks.