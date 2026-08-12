------------------------ MODULE MCEPBSMultiSlotV2 ------------------------
EXTENDS EPBSMultiSlotV2

ConstInit ==
    /\ Validators         = {"v1", "v2", "v3", "v4", "v5"}
    /\ ByzValidators      = {"v5"}
    /\ ProposerBoost      = 2
    /\ MaxDepth      = 4
    /\ ReorgHeadWeightAbs = 2
    /\ MaxEquivocations   = 1

===========================================================================
