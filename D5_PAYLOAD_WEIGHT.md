# D5 — `PayloadWeight` is phantom: Gloas adds no payload term to fork-choice weight

**Status: CONFIRMED by reading the spec. Blocks republication of `SCALING_RESPONSE.md`.**

Source: `ethereum/consensus-specs`, `specs/gloas/fork-choice.md`, fetched to
`.cache/specs/gloas-fork-choice.md`.

## What the spec does

`get_weight` returns attestation score plus, conditionally, proposer score:

```python
def get_weight(store: Store, node: ForkChoiceNode) -> Gwei:
    if is_previous_slot_payload_decision(store, node):
        return Gwei(0)
    state = store.checkpoint_states[store.justified_checkpoint]
    attestation_score = get_attestation_score(store, node, state)
    if not should_apply_proposer_boost(store):
        return attestation_score
    proposer_score = Gwei(0)
    proposer_boost_node = ForkChoiceNode(
        root=store.proposer_boost_root, payload_status=PAYLOAD_STATUS_PENDING)
    if is_ancestor(store, proposer_boost_node, node):
        proposer_score = get_proposer_score(store)
    return attestation_score + proposer_score
```

**There is no payload term.** A grep for `payload.*score|PAYLOAD.*BOOST|payload_boost`
across the file returns nothing.

Payload timeliness enters fork choice through node identity instead:

```python
def get_node_children(store, blocks, node):
    if node.payload_status == PAYLOAD_STATUS_PENDING:
        children = [ForkChoiceNode(root=node.root, payload_status=PAYLOAD_STATUS_EMPTY)]
        if is_payload_verified(store, node.root):
            children.append(ForkChoiceNode(root=node.root, payload_status=PAYLOAD_STATUS_FULL))
        return children
    ...
```

Every block yields **two candidate nodes**, full and empty. The PTC verdict decides
whether the FULL node exists as a candidate; `get_head` then uses
`get_payload_status_tiebreaker` to choose between full and empty. It is node
availability plus a tiebreaker, not additive weight.

## What we modelled

```tla
PayloadWeight(b) == IF ptcVerdict[b] = "present" THEN PayloadBoost ELSE 0
```

A quantity with no counterpart in the specification. D2 then propagated it to every
ancestor's subtree weight, compounding the error.

**This predates the composed model.** `EPBSForkChoice.tla` carried `PayloadBoost` as a
`CONSTANT` in the original ESP submission, and `SCALING_RESPONSE.md` §2 describes it as
"a committee verdict feeding directly into fork-choice weight". The coupling between
the PTC and fork choice is real; the mechanism we gave it is not.

## What this invalidates

- **The stickiness result.** Reorg reachability moving from 2,692 states to
  unreachable in 19,889,946 after D2 was measured while propagating phantom weight.
  It is probably an artifact and must be re-measured with `PayloadWeight` removed.
- **§2 of `SCALING_RESPONSE.md`**, which presents the payload-boost coupling as the
  interaction the ESP review said was unreachable.
- **Any conclusion about payload-timely blocks resisting reorg**, since the
  resistance was manufactured by weight the protocol does not grant.

## Two further gaps found in the same read

- `is_previous_slot_payload_decision(store, node) => weight 0`. An entire weight-zeroing
  rule, unmodelled.
- `should_apply_proposer_boost(store)` gates proposer boost. We apply it
  unconditionally to the designated proposal of the current slot.

## How to verify before republication

1. `grep -nE "payload.*score|PAYLOAD.*BOOST" .cache/specs/gloas-fork-choice.md`
   — expect no hits.
2. Read `get_weight` and confirm the return is `attestation_score + proposer_score`.
3. Read `get_node_children` and `get_payload_status_tiebreaker` and confirm payload
   status is a node attribute.

## Fix, and its size

This is not a patch. Faithful modelling requires fork-choice nodes to be
`(root, payload_status)` pairs rather than block ids, with `Children` returning
full/empty variants and a tiebreaker between them. That changes the type of every
fork-choice operator, the vote store, and `blockAnc`.

Interim honest option: delete `PayloadWeight` entirely, re-run the probe suite, and
report the model as having no PTC-to-fork-choice coupling at all — accurate about
what it does model, and explicit that the coupling is future work.

**Until one of those is done, `SCALING_RESPONSE.md` must not be published or sent.**
