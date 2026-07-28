# Scaling Evidence

The default configurations are deliberately small so the state space is tiny and the checks run in a second (good for CI). A fair question is whether the properties hold beyond toy sizes. They do. The larger configurations below were run with TLC and all pass with no error.

The Coq developments already cover the payment core and the reorg threshold for **all** sizes and weights, so scaling matters most for the properties that only TLC checks: the temporal behavior (liveness), the timed PTC tally, and multi-slot draining.

| Model | Configuration | Distinct states | Result |
|---|---|---|---|
| `EPBS.tla` | default (2 builders, 3 attesters, values {1,2}) | 207 | no error |
| `EPBS.tla` | `EPBS_large.cfg` (3 builders, 5 attesters, values {1,2,3}) | 4,704 | no error |
| `EPBSPTC.tla` | default (3 attesters, 1 Byzantine, threshold 2) | 36 | no error |
| `EPBSPTC.tla` | `EPBSPTC_large.cfg` (5 attesters, 2 Byzantine, threshold 3) | 180 | no error |
| `EPBSChain.tla` | default (3 slots) | 53 | no error |
| `EPBSChain.tla` | `EPBSChain_large.cfg` (6 slots) | 267 | no error |

Every invariant and liveness property in each model held at the larger size, including the honest-majority PTC margin (5 attesters, 2 Byzantine, threshold 3) and a chain twice as long.

## Reproduce

```bash
# tla2tools.jar from https://github.com/tlaplus/tlaplus/releases
java -cp tla2tools.jar tlc2.TLC -config specs/EPBS_large.cfg       specs/EPBS.tla
java -cp tla2tools.jar tlc2.TLC -config specs/EPBSPTC_large.cfg    specs/EPBSPTC.tla
java -cp tla2tools.jar tlc2.TLC -config specs/EPBSChain_large.cfg  specs/EPBSChain.tla
```

The default (small) configurations remain the ones run by `verify.sh` and CI, so the automated check stays fast; these larger runs are supplementary evidence.
