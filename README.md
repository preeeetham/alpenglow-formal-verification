# Alpenglow Formal Verification

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![TLA+](https://img.shields.io/badge/TLA+-Specification-orange.svg)](https://lamport.azurewebsites.net/tla/tla.html)
[![Rust](https://img.shields.io/badge/Rust-Stateright-red.svg)](https://www.stateright.rs/)

Formal verification of Solana's Alpenglow consensus protocol using TLA+ and Stateright frameworks.

## Overview

This project provides machine-verifiable formal proofs for the Alpenglow consensus protocol, Solana's next-generation consensus mechanism that delivers:

- **100-150ms finalization** (100x faster than current TowerBFT)
- **Dual-path consensus**: Fast path with 80% stake, conservative path with 60% stake
- **Optimized block propagation**: Erasure-coded single-hop distribution
- **"20+20" resilience**: Tolerates 20% Byzantine + 20% crashed nodes

## Project Structure

```
alpenglow-formal-verification/
├── specs/                       # Formal specifications
│   ├── tlaplus/                # TLA+ specifications
│   └── stateright/             # Stateright specifications
├── proofs/                     # Verification results
│   ├── safety/                 # Safety property proofs
│   ├── liveness/               # Liveness property proofs
│   └── resilience/             # Resilience property proofs
├── model-checking/             # Model checking configurations
│   ├── small-config/           # 4-10 nodes verification
│   └── statistical/            # Large-scale validation
├── docs/                       # Documentation
└── experiments/               # Validation experiments
```

## Key Components

### Votor (Voting Component)
- Fast path finalization with ≥80% stake participation
- Slow path finalization with ≥60% stake participation
- Concurrent execution with min(δ₈₀%, 2δ₆₀%) finalization time

### Rotor (Block Distribution Component)
- Reed-Solomon erasure coding (Γ=64, γ=32)
- Stake-weighted relay sampling (PS-P algorithm)
- Merkle tree authentication
- UDP-based message distribution

## Verification Properties

### Safety Properties
- No conflicting blocks finalized
- Chain consistency
- Certificate uniqueness

### Liveness Properties
- Progress under partial synchrony
- Fast path completion
- Bounded finalization time

### Resilience Properties
- Byzantine fault tolerance (<20% Byzantine stake)
- Crash fault tolerance (<20% crashed stake)
- Network partition recovery

## Getting Started

### Prerequisites

- Java 11+ (for TLA+ tools)
- Rust 1.70+ (for Stateright)
- VSCode with TLA+ extension (optional)

### Installation

1. Clone the repository:
```bash
git clone https://github.com/your-username/alpenglow-formal-verification.git
cd alpenglow-formal-verification
```

2. Install TLA+ tools:
```bash
# Download TLA+ tools
wget https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
wget https://github.com/tlaplus/tlaplus/releases/latest/download/tlc2.jar
```

3. Install Rust (for Stateright):
```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

### Running Verification

#### TLA+ Approach
```bash
# Run model checker
java -jar tlc2.jar -config specs/tlaplus/AlpenglowConsensus.cfg specs/tlaplus/AlpenglowConsensus.tla
```

#### Stateright Approach
```bash
cd specs/stateright
cargo test
cargo run --bin model-checker
```

## Development Status

- [x] Project structure setup
- [ ] Core specifications
- [ ] Safety properties verification
- [ ] Liveness properties verification
- [ ] Resilience properties verification
- [ ] Large-scale validation
- [ ] Documentation and reports

## Contributing

This project is open source under the Apache 2.0 license. Contributions are welcome!

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests and verification
5. Submit a pull request

## References

- [Alpenglow Whitepaper](https://github.com/solana-labs/alpenglow)
- [TLA+ Homepage](https://lamport.azurewebsites.net/tla/tla.html)
- [Stateright Book](https://www.stateright.rs/)
- [Solana Documentation](https://docs.solana.com/)

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for details.
