/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MorphismPropertiesExamples.RelativeBaseChange
public import MorphismPropertiesExamples.OverPullback
public import MorphismPropertiesExamples.PullbackMap
public import MorphismPropertiesExamples.IdentityClosure
public import MorphismPropertiesExamples.PullbackAssociativity
public import MorphismPropertiesExamples.Density

/-!
# Examples of relative pullback preservation

Constructed examples on finite chains and nonempty finite subsets, including
failure of absolute stability and of unrelated pullback existence along the same
base arrow, and composition/base-change stability without identity closure.
The structured-over examples exercise projections and uniqueness.
-/

@[expose] public section
