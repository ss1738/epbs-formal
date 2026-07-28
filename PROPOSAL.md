# Brief: Formal Verification of Enshrined PBS (ePBS)

A short brief for an Ethereum Foundation Ecosystem Support Program (ESP) Office Hours conversation. Not a final application. The goal of the first conversation is to confirm scope and fit before a full proposal.

## One sentence

An open-source, machine-checkable formal model of Enshrined Proposer-Builder Separation that states the safety and liveness properties of the mechanism precisely and checks them, so consensus-level flaws are found before Glamsterdam enshrines them.

## The problem

ePBS moves the proposer/builder split out of relays (MEV-Boost) and into the Ethereum protocol. That is a change to how blocks are proposed at layer 1. A subtle error, for example a way for a builder to be paid without revealing, to grief a proposer, or to substitute a payload after commitment, is catastrophic and cannot be rolled back once shipped. The natural time to catch such errors is while the spec is still being finalized.

## What this delivers

A TLA+ model of one ePBS slot with an explicit adversary (Byzantine builders that withhold or equivocate, a Byzantine PTC minority that lies), and a catalog of eight safety invariants and two liveness properties, checked with the TLC model checker. See `PROPERTIES.md`. The strongest invariants are then proven for all instance sizes in a follow-on milestone.

The properties include:

- Payment safety: the proposer is paid unconditionally on inclusion, even if the builder never reveals.
- Commitment binding: the canonical payload is always the one the proposer committed to.
- Equivocation slashing: a non-committed reveal is slashed and rejected.
- No reorg on withhold: a withholding builder yields an empty slot without unwinding the proposer's block.
- Liveness: the slot always terminates, and honest timely work is never dropped under an honest PTC majority.

## Why this fits ESP

- It is a public good, MIT-licensed, for builders and spec authors, not an end-user product and not commercial.
- It targets a live roadmap item (ePBS / Glamsterdam) at the moment it is most useful, before enshrinement.
- It falls under the Research and Infrastructure funding categories.
- It is scoped for a solo researcher: each milestone is a complete artifact on its own.

## Why this applicant

The author works in exactly the two areas this needs. Formal methods: models and proofs in Coq and TLA+. Applied cryptography and consensus: a from-scratch Rust layer-1 with BLS aggregate signatures, on-chain BLS via EIP-2537, KZG and Verkle commitments, Groth16 and Nova proof systems, and a Groth16 verifier already deployed and verified on public Ethereum. This is the rare intersection of formal verification and protocol-level cryptography that ePBS safety analysis requires.

## Milestone 1 (the fundable unit)

Run the single-slot model through TLC, publish the result and any counterexamples with fixes, and write up coverage. Weeks of work, and it stands alone. See `MILESTONES.md` for the full plan.

## What is asked

A short Office Hours conversation to confirm scope and fit, and guidance on which ePBS spec revision to target so the model tracks the version headed for enshrinement.

## Links

- Repository: this repo (open-source, MIT).
- Prior work: a Groth16 verifiable-private-state verifier, live and verified on public Ethereum.
