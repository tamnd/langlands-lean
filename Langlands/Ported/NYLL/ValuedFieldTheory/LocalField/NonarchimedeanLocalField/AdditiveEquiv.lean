/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
-- Ported from n-yamaguchi-0729/ClassFieldTheory at commit fc644f42dade5bdc7157fc3ef2eef4dbf2d6a565, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/AdditiveEquiv.lean`. The module prefix is `Langlands.Ported.NYLL` in place of `Nyll`. The changes for the Mathlib of the project pin are in manifests/ported.yaml.


module

public import Mathlib.Algebra.Group.Equiv.TypeTags
/-!
# Additive recoding of multiplicative equivalences

Turns a multiplicative group equivalence into the corresponding equivalence
between the additive recodings of its source and target.
-/

@[expose] public section

namespace LocalFieldTheory

noncomputable section

universe u v

/-- Transport a multiplicative equivalence to an additive equivalence. -/
def additiveEquivOfMulEquiv {A : Type u} {B : Type v} [Group A] [Group B] (e : A ≃* B) :
    Additive A ≃+ Additive B :=
  MulEquiv.toAdditive e

end
end LocalFieldTheory
