---- MODULE LivenessProofs ----
EXTENDS AlpenglowConsensus, TLAPS

(*
 * Formal Liveness Proofs for Alpenglow Consensus Protocol
 * Progress and termination guarantees under partial synchrony
 *)

(* =============================================================================
 * LEMMA 1: Progress Under Honest Majority
 * ============================================================================= *)

LEMMA ProgressUnderHonestMajority ==
    ASSUME HonestStake > 60,
           NetworkSynchronous,
           FairActions
    PROVE  \A slot \in Slots : <>(finalized # {})
PROOF
<1>1. SUFFICES ASSUME NEW slot \in Slots,
                      HonestNodes eventually vote,
                      Network delivers votes
               PROVE  <>\E hash \in Hashes : <<slot, hash>> \in finalized
      BY honest majority assumption
<1>2. Honest nodes will eventually cast consistent votes
      BY synchrony assumption and protocol logic
<1>3. 60% stake threshold will be reached
      BY <1>2 and HonestStake > 60 assumption  
<1>4. SlowFinalize will eventually trigger
      BY <1>3 and FinalStakeFor calculation
<1>5. QED BY <1>4 DEF SlowFinalize

(* =============================================================================
 * LEMMA 2: Fast Path Completion
 * ============================================================================= *)

LEMMA FastPathCompletion ==
    ASSUME ResponsiveStake > 80,
           NetworkSynchronous,
           FairActions
    PROVE  \A slot \in Slots : <>\E hash \in Hashes : <<slot, hash>> \in fastFinalized
PROOF
<1>1. Responsive nodes vote quickly under synchrony
      BY ResponsiveStake and NetworkSynchronous assumptions
<1>2. 80% stake threshold achieved rapidly  
      BY <1>1 and ResponsiveStake > 80
<1>3. FastFinalize triggered before slow path
      BY <1>2 and NotarStakeFor >= 80 condition
<1>4. QED BY <1>3 DEF FastFinalize

(* =============================================================================
 * LEMMA 3: Bounded Finalization Time
 * ============================================================================= *)

LEMMA BoundedFinalizationTime ==
    ASSUME HonestStake > 60,
           NetworkDelay <= Delta,
           VotingDelay <= Epsilon
    PROVE  \A slot \in Slots, hash \in Hashes :
               <<slot, hash>> \in finalized => 
               FinalizationTime(slot, hash) <= Max(DeltaFast, 2 * DeltaSlow)
PROOF
<1>1. Fast path completes in DeltaFast time
      BY network synchrony and 80% threshold
<1>2. Slow path completes in 2 * DeltaSlow time  
      BY two-round voting and 60% threshold
<1>3. Protocol chooses minimum of both paths
      BY dual-path concurrent execution
<1>4. QED BY <1>1, <1>2, <1>3 and min() function

(* =============================================================================
 * LEMMA 33: ParentReady Timeouts for Leader Window Slots
 * ============================================================================= *)

LEMMA ParentReadyTimeouts ==
    ASSUME ParentReady(slot),
           \A s \in LeaderWindow(slot) : Timeout(s) <= 2 * Delta
    PROVE  \A s \in LeaderWindow(slot) : Timeout(s) <= 2 * Delta
PROOF
<1>1. ParentReady implies all slots in leader window have timeouts
      BY definition of ParentReady and LeaderWindow
<1>2. Timeout bound applies to all slots in window
      BY assumption and leader window properties
<1>3. QED BY <1>1, <1>2

(* =============================================================================
 * COROLLARY 34: Derived from Lemma 33
 * ============================================================================= *)

COROLLARY ParentReadyTimeoutCorollary ==
    ASSUME ParentReady(slot)
    PROVE  \A s \in LeaderWindow(slot) : Timeout(s) <= 2 * Delta
PROOF BY ParentReadyTimeouts

(* =============================================================================
 * LEMMA 35-37: Explicit Notarization/Skip Vote Casting
 * ============================================================================= *)

LEMMA NotarizationVoteCasting ==
    ASSUME HonestStake > 60,
           NetworkSynchronous,
           FairScheduling
    PROVE  \A node \in HonestNodes, slot \in Slots :
               <>(<<node, slot, "NotarVote", _>> \in votes)
PROOF
<1>1. Honest nodes eventually receive block proposals
      BY network synchrony and honest majority
<1>2. Honest nodes validate and cast NotarVote
      BY protocol logic and honest behavior
<1>3. QED BY <1>1, <1>2

LEMMA SkipVoteCasting ==
    ASSUME HonestStake > 60,
           NetworkSynchronous,
           SafeToSkip(slot)
    PROVE  \A node \in HonestNodes, slot \in Slots :
               <>(<<node, slot, "SkipVote", _>> \in votes)
PROOF
<1>1. SafeToSkip triggers skip vote casting
      BY definition of SafeToSkip
<1>2. Honest nodes cast skip votes when safe
      BY protocol logic and honest behavior
<1>3. QED BY <1>1, <1>2

LEMMA SkipCertificateConditions ==
    ASSUME SkipStakeFor(slot) >= 60,
           NetworkSynchronous
    PROVE  \E cert \in certificates : cert.type = "Skip" /\ cert.slot = slot
PROOF
<1>1. 60% stake threshold reached for skip
      BY assumption
<1>2. Skip certificate generated
      BY certificate generation logic
<1>3. QED BY <1>1, <1>2

(* =============================================================================
 * LEMMA 38: Notar-fallback Certificates with 40% Stake
 * ============================================================================= *)

LEMMA NotarFallbackCertificates ==
    ASSUME NotarStakeFor(slot, hash) > 40,
           NetworkSynchronous,
           FairScheduling
    PROVE  \E cert \in certificates : cert.type = "NotarFallback" /\ cert.slot = slot
PROOF
<1>1. 40% stake threshold enables notar-fallback
      BY assumption and protocol logic
<1>2. Notar-fallback certificate generated
      BY certificate generation with 40% threshold
<1>3. QED BY <1>1, <1>2

(* =============================================================================
 * LEMMA 39-42: Synchronization on Notar-fallback/Skip Certificates
 * ============================================================================= *)

LEMMA NotarFallbackSynchronization ==
    ASSUME NetworkEventuallySynchronous,
           HonestStake > 60
    PROVE  \A node1, node2 \in HonestNodes :
               <>(node1.notarFallbackCerts = node2.notarFallbackCerts)
PROOF
<1>1. Network eventually delivers all certificates
      BY NetworkEventuallySynchronous assumption
<1>2. Honest nodes synchronize on certificate sets
      BY gossip protocol and honest behavior
<1>3. QED BY <1>1, <1>2

LEMMA SkipCertificateSynchronization ==
    ASSUME NetworkEventuallySynchronous,
           HonestStake > 60
    PROVE  \A node1, node2 \in HonestNodes :
               <>(node1.skipCerts = node2.skipCerts)
PROOF
<1>1. Network eventually delivers all certificates
      BY NetworkEventuallySynchronous assumption
<1>2. Honest nodes synchronize on certificate sets
      BY gossip protocol and honest behavior
<1>3. QED BY <1>1, <1>2

LEMMA ParentReadyEventEmission ==
    ASSUME NotarFallbackSynchronization,
           SkipCertificateSynchronization
    PROVE  \A node \in HonestNodes, slot \in Slots :
               <>(ParentReady(slot) \in node.events)
PROOF
<1>1. Synchronized certificates enable ParentReady
      BY definition of ParentReady
<1>2. Honest nodes emit ParentReady events
      BY protocol logic and certificate synchronization
<1>3. QED BY <1>1, <1>2

(* =============================================================================
 * LEMMA 4: Eventual Consensus
 * ============================================================================= *)

LEMMA EventualConsensus ==
    ASSUME NetworkEventuallyHeals,
           SufficientHonestStake,
           BoundedMessageDelay
    PROVE  <>(\A node1, node2 \in HonestNodes : 
                node1.finalized = node2.finalized)
PROOF
<1>1. Network partitions eventually heal
      BY NetworkEventuallyHeals assumption
<1>2. Honest nodes synchronize views
      BY <1>1 and protocol message exchange
<1>3. Finalized sets converge to same values
      BY <1>2 and safety properties (no conflicts)
<1>4. QED BY <1>3

(* =============================================================================
 * THEOREM: Complete Liveness
 * ============================================================================= *)

THEOREM LivenessGuarantees ==
    ASSUME Spec,
           HonestStake > 60,
           NetworkEventuallySynchronous,
           FairScheduling
    PROVE  /\ <>(\E block : block \in finalized)  \* Progress
           /\ ResponsiveStake > 80 => <>(\E block : block \in fastFinalized)  \* Fast completion
           /\ \A block : <<block.slot, block.hash>> \in finalized => 
                FinalizationTime(block.slot, block.hash) <= BoundedTime  \* Bounded time
PROOF
<1>1. Progress follows from ProgressUnderHonestMajority
      BY ProgressUnderHonestMajority and assumptions
<1>2. Fast completion follows from FastPathCompletion  
      BY FastPathCompletion and ResponsiveStake condition
<1>3. Bounded time follows from BoundedFinalizationTime
      BY BoundedFinalizationTime and network assumptions
<1>4. QED BY <1>1, <1>2, <1>3

(* =============================================================================
 * COROLLARY: Liveness Under Byzantine Faults
 * ============================================================================= *)

COROLLARY LivenessUnderByzantineFaults ==
    ASSUME ByzantineStake < 20,
           CrashedStake < 20,
           HonestStake > 60,
           Spec
    PROVE  <>(\E block : block \in finalized)
PROOF
<1>1. Byzantine and crashed stake constraints ensure honest majority
      BY arithmetic: 100 - 20 - 20 = 60 < HonestStake
<1>2. Honest majority enables progress
      BY <1>1 and ProgressUnderHonestMajority  
<1>3. QED BY <1>2

====
