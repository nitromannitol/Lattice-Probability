/-
# Rellich assembly (quarantined)

This module formerly assembled `rkLowFreqNet` from the `C^m`-net residual `BandLimitedCmNet`, a
wrapper for the refuted `rkUniformCmNet`.  That route is **false**: `rkUniformCmNet` asks the rough
fields themselves to be `C^m`-close, which fails once `s < m` (`RellichLowFreqNet.lean`), and its
declarations `rkUniformCmNet` / `rkLowFreqNet_of_uniformCmNet` have been removed from
`RellichCmNetReduction.lean`.  The route is quarantined here and must not be revived.

The sound route to `rkLowFreqNet` is `RellichLowFreqGlue.lean`
(`rkLowFreqNet_of_truncation_and_supportRepair`).
-/
