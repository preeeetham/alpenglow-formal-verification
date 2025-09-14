# 🎬 Video Walkthrough Quick Reference

## 🚀 **Start Here: Opening Hook**
**File**: `README.md`  
**Key Message**: "World's first complete formal verification of Alpenglow consensus protocol"  
**Visual**: GitHub repository with 100% coverage badge

## 🏗️ **Part 1: Project Architecture (1-3 min)**
**Files to Show**:
- Project file tree structure
- `README.md` - Key components section
- `docs/technical-report.md` - Executive summary

**Key Points**:
- Votor (dual-path voting)
- Rotor (erasure-coded distribution)
- "20+20" resilience model

## 🎯 **Part 2: The Challenge (3-5 min)**
**Files to Show**:
- `docs/technical-report.md` - Whitepaper lemma mapping table
- Alpenglow whitepaper PDF (if available)
- `specs/tlaplus/` directory structure

**Key Points**:
- 47+ lemmas and theorems to verify
- Mathematical rigor required
- TLA+ and TLAPS approach

## 🏆 **Part 3: 100% Coverage Achievement (5-8 min)**
**Files to Show**:
- `docs/technical-report.md` - Complete coverage table
- `proofs/safety/SafetyProofs.tla` - Safety lemmas
- `proofs/liveness/LivenessProofs.tla` - Liveness lemmas
- `proofs/committee/CommitteeSamplingProofs.tla` - Committee proofs
- `specs/tlaplus/Rotor.tla` - Rotor optimization proofs

**Key Points**:
- All 8 safety lemmas proven
- All 6 liveness lemmas proven
- All 2 committee sampling lemmas proven
- All 2 Rotor optimization aspects proven

## 🔧 **Part 4: Live Demo (8-12 min)**
**Commands to Run**:
```bash
# 1. Environment check
java -version
python3 --version

# 2. Quick test
python3 test_verification.py

# 3. Safety verification
java -cp tla2tools.jar tlc2.TLC -config model-checking/small-config/AlpenglowConsensus.cfg model-checking/small-config/AlpenglowConsensus.tla

# 4. Show results
cat EXPERIMENT_RESULTS.json
```

**Files to Open**:
- `proofs/safety/SafetyProofs.tla` - Show VoteExclusivity lemma
- `proofs/committee/CommitteeSamplingProofs.tla` - Show PS_P_Security lemma
- `VERIFICATION_RESULTS.md` - Show key metrics

## 📊 **Part 5: Results & Impact (12-15 min)**
**Files to Show**:
- `VERIFICATION_RESULTS.md` - Key metrics
- `docs/technical-report.md` - Detailed results
- `.github/workflows/verify.yml` - CI/CD pipeline

**Key Metrics**:
- 9,698,927+ states explored
- 100% whitepaper coverage
- All safety/liveness properties verified
- Production-ready framework

## 🚀 **Part 6: Future Implications (15-17 min)**
**Files to Show**:
- `PROJECT_OVERVIEW.md` - Project impact
- GitHub repository - Open source community
- `LICENSE` - Apache 2.0 license

**Key Points**:
- Industry standard for consensus verification
- Open source for community use
- Methodology applicable to other protocols

## 🎯 **Part 7: Conclusion (17-20 min)**
**Files to Show**:
- `README.md` - Final summary
- GitHub repository - Call to action
- Contact information

**Key Messages**:
- World's first complete formal verification
- 100% whitepaper coverage achieved
- Open source community engagement

---

## 🎬 **Production Checklist**

### **Before Recording**:
- [ ] All verification commands tested and working
- [ ] Key files open and ready to show
- [ ] Terminal with commands pre-typed
- [ ] Screen recording software ready
- [ ] Audio equipment tested

### **During Recording**:
- [ ] Clear, confident speaking pace
- [ ] Smooth transitions between sections
- [ ] Highlight key achievements prominently
- [ ] Show live verification results
- [ ] Maintain professional presentation style

### **After Recording**:
- [ ] Review for clarity and flow
- [ ] Add captions if needed
- [ ] Upload to appropriate platform
- [ ] Share with community

---

## 🎯 **Key Success Factors**

1. **Start Strong**: Hook audience with 100% coverage achievement
2. **Show Don't Tell**: Live verification demonstrations
3. **Highlight Impact**: Mathematical rigor and production readiness
4. **Call to Action**: Community engagement and open source
5. **Professional Quality**: Clear audio, good visuals, smooth flow

**Total Duration**: 20 minutes  
**Target**: Technical audience  
**Goal**: Showcase complete formal verification achievement
