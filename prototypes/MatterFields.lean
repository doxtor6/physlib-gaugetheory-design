import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.Pi

/-!
# Prototype: restriction of matter fields, and the two conditions under every construction

Compiled against the branch of physlib PR #2011 (commit `800e1cf6`), Lean v4.35.0, with
`lake env lean MatterFields.lean`. Not part of Physlib; a design check.

## Part 1. Restriction along a morphism of gauge data

For a morphism of local gauge data `φ : Hom jets jets'`, a matter field over `jets'` is a
matter field over `jets` (`MatterField.comap`): the same value space and Lorentz action, the
jets of `jets` acting through `φ.groupJ` and its gauge algebra through `φ.lie`. The law that
the gauge-algebra action generates the jet action transports, because `Hom` commutes with
every map the law mentions (`Hom.lie_adjointCoeff`,
`Hom.lie_evalLie_iteratedDeriv_maurerCartan`).

## Part 2. The two conditions are preserved

`MatterField.PureJetsActTrivially` and `MatterField.GaugeLorentzCompatible` pass to the
restriction `comap`, to the direct sum `prod` of two matter fields and to the direct sum
`pi` of a finite family. With the table rows of `Covariance.lean`, every construction of
matter fields in the library preserves them.
-/

open TensorProduct Matrix MatrixGroups GaugeAlgebraRealization

/-! ## Part 1. Restriction along a morphism of gauge data -/

namespace LocalGaugeData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {G₀' : Type} [Group G₀'] {𝔤' : Type} [LieRing 𝔤'] [LieAlgebra ℝ 𝔤']
  {GJ' : Type} [Group GJ'] {𝔤J' : Type} [LieRing 𝔤J'] [LieAlgebra ℝ 𝔤J']
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {jets' : LocalGaugeData G₀' 𝔤' GJ' 𝔤J'}

/-- A morphism carries the adjoint Taylor coefficients across. -/
lemma Hom.lie_adjointCoeff (φ : Hom jets jets') (U : GJ) (x : Multiset (Fin 1 ⊕ Fin 3)) (c : 𝔤) :
    φ.lie (jets.adjointCoeff U x c) = jets'.adjointCoeff (φ.groupJ U) x (φ.lie c) := by
  rw [adjointCoeff_apply, adjointCoeff_apply, ← φ.evalLie_lieJ, φ.lieJ_iteratedDeriv,
    φ.lieJ_adjointJ, φ.lieJ_ofConstantLie]

/-- A morphism carries the base-point Taylor data of the Maurer–Cartan form across. -/
lemma Hom.lie_evalLie_iteratedDeriv_maurerCartan (φ : Hom jets jets') (U : GJ)
    (μ : Fin 1 ⊕ Fin 3) (p : Multiset (Fin 1 ⊕ Fin 3)) :
    φ.lie (jets.evalLie (jets.iteratedDeriv p (jets.maurerCartan U μ)))
      = jets'.evalLie (jets'.iteratedDeriv p (jets'.maurerCartan (φ.groupJ U) μ)) := by
  rw [← φ.evalLie_lieJ, φ.lieJ_iteratedDeriv, φ.lieJ_maurerCartan]

end LocalGaugeData

namespace MatterField

open LocalGaugeData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {G₀' : Type} [Group G₀'] {𝔤' : Type} [LieRing 𝔤'] [LieAlgebra ℝ 𝔤']
  {GJ' : Type} [Group GJ'] {𝔤J' : Type} [LieRing 𝔤J'] [LieAlgebra ℝ 𝔤J']
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {jets' : LocalGaugeData G₀' 𝔤' GJ' 𝔤J'}

/-- **Restriction along a morphism of gauge data**: a matter field over `jets'` is a matter
  field over `jets`, the jets of `jets` acting through `φ.groupJ` and its gauge algebra
  through `φ.lie`. -/
noncomputable def comap (φ : Hom jets jets') (M : MatterField jets') : MatterField jets where
  V := M.V
  repLorentz := M.repLorentz
  repJet := M.repJet.comp φ.groupJ
  repAlgebra := M.repAlgebra.comp φ.lie.toLinearMap
  repJet_smul U χ z := M.repJet_smul (φ.groupJ U) χ z
  repAlgebra_isInfinitesimalAction :=
    { repCoeff_cons := fun U μ x => by
        have h := M.repAlgebra_isInfinitesimalAction.repCoeff_cons (φ.groupJ U) μ x
        simp only [LinearMap.comp_apply, LieHom.coe_toLinearMap,
          φ.lie_evalLie_iteratedDeriv_maurerCartan]
        exact h
      repCoeff_act := fun U x c => by
        have h := M.repAlgebra_isInfinitesimalAction.repCoeff_act (φ.groupJ U) x (φ.lie c)
        simp only [LinearMap.comp_apply, LieHom.coe_toLinearMap, φ.lie_adjointCoeff]
        exact h }
  massWeight := M.massWeight
  statistic := M.statistic

@[simp] lemma comap_V (φ : Hom jets jets') (M : MatterField jets') : (M.comap φ).V = M.V := rfl

/-- Restriction preserves the base-point condition. -/
lemma comap_pureJetsActTrivially (φ : Hom jets jets') (M : MatterField jets')
    (h : M.PureJetsActTrivially) : (M.comap φ).PureJetsActTrivially := by
  intro W hW
  exact h (W := φ.groupJ W) (by rw [φ.eval_groupJ, hW, map_one])

/-- Restriction preserves the commutation of the gauge and Lorentz actions. -/
lemma comap_gaugeLorentzCompatible (φ : Hom jets jets') (M : MatterField jets')
    (h : M.GaugeLorentzCompatible) : (M.comap φ).GaugeLorentzCompatible :=
  fun c Λ v => h (φ.lie c) Λ v

/-- Restriction along the identity is the identity, up to the evident equality of fields. -/
example (M : MatterField jets) : (M.comap (Hom.id jets)).repJet = M.repJet := rfl

end MatterField

/-! ## Part 2. Direct sums preserve the two conditions -/

namespace MatterField

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

/-- The direct sum of two matter fields satisfies the base-point condition when both do. -/
lemma prod_pureJetsActTrivially (M N : MatterField jets) (h : M.massWeight = N.massWeight)
    (hσ : M.statistic = N.statistic) (hM : M.PureJetsActTrivially)
    (hN : N.PureJetsActTrivially) : (M.prod N h hσ).PureJetsActTrivially := by
  intro W hW
  show GaugeAlgebraRealization.repCoeff (repJetProd M N) W 0 = LinearMap.id
  rw [repCoeff_repJetProd, hM hW, hN hW]
  exact LinearMap.ext fun p => rfl

/-- The direct sum of two matter fields satisfies gauge–Lorentz compatibility when both do. -/
lemma prod_gaugeLorentzCompatible (M N : MatterField jets) (h : M.massWeight = N.massWeight)
    (hσ : M.statistic = N.statistic) (hM : M.GaugeLorentzCompatible)
    (hN : N.GaugeLorentzCompatible) : (M.prod N h hσ).GaugeLorentzCompatible :=
  fun c Λ v => Prod.ext (hM c Λ v.1) (hN c Λ v.2)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → MatterField jets)

/-- The direct sum of a finite family satisfies the base-point condition when every summand
  does. -/
lemma pi_pureJetsActTrivially (w : ℕ) (h : ∀ i, (M i).massWeight = w) (σ : FieldStatistic)
    (hσ : ∀ i, (M i).statistic = σ) (hM : ∀ i, (M i).PureJetsActTrivially) :
    (MatterField.pi M w h σ hσ).PureJetsActTrivially := by
  intro W hW
  show GaugeAlgebraRealization.repCoeff (repJetPi M) W 0 = LinearMap.id
  rw [repCoeff_repJetPi]
  refine LinearMap.ext fun p => funext fun i => ?_
  show GaugeAlgebraRealization.repCoeff (M i).repJet W 0 (p i) = p i
  rw [hM i hW]
  rfl

/-- The direct sum of a finite family satisfies gauge–Lorentz compatibility when every
  summand does. -/
lemma pi_gaugeLorentzCompatible (w : ℕ) (h : ∀ i, (M i).massWeight = w) (σ : FieldStatistic)
    (hσ : ∀ i, (M i).statistic = σ) (hM : ∀ i, (M i).GaugeLorentzCompatible) :
    (MatterField.pi M w h σ hσ).GaugeLorentzCompatible :=
  fun c Λ v => funext fun i => hM i c Λ (v i)

end MatterField

#print axioms MatterField.comap
#print axioms MatterField.comap_pureJetsActTrivially
#print axioms MatterField.prod_pureJetsActTrivially
#print axioms MatterField.pi_pureJetsActTrivially
#print axioms MatterField.pi_gaugeLorentzCompatible
