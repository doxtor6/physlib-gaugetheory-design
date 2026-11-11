import PhyslibAlpha.Particles.StandardModel.Basic
import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalCovField.Basic
import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalField.MassWeight

/-!
# Prototype: covariance for every card

Compiled against the branch of physlib PR #2011 (commit `800e1cf6`), Lean v4.35.0, with
`lake env lean Covariance.lean`. Not part of Physlib; a design check.

## Part 1. One evaluation law gives `PureJetsActTrivially` for every table row

`MatrixRep.matterField_pureJetsActTrivially` needs the matrix of a jet with trivial value
to have identity constant term, which the axioms of `MatrixRep`, `U1Factor` and `SUFactor`
do not imply. Stated as a law (`EvalLaw`), it is preserved by every construction of the
table layer and holds for the canonical factors of `ofFactors`, so every row of every
table satisfies `MatterField.PureJetsActTrivially`, with no model-specific proof.

## Part 2. The covariant reduction theorem for an arbitrary field datum

For free gauge data and species on which pure jets act trivially at the base point, an
element of `J(T)` fixed by all jets of gauge transformations lies in the covariant field
algebra (`mem_localCovFieldAlgebra_of_gaugeInvariant`), and jet-gauge invariance is
covariance together with global invariance (`forall_repJet_eq_iff`). The proof assembles
three results that are already generic:

* `GaugeAlgebraRealization.invariant_mem_adjoin_fieldStrength`, the reduction for the gauge
  field in the presence of further generators fixed by the pure jets;
* `GaugeAlgebraRealization.adjoin_symbols_eq_adjoin_covDerivIter`, the span lemma exchanging
  the derivative symbols of a matter family for its covariant tower;
* the gauge laws of the covariant towers in `J(T)`.

## Part 3. The Standard Model card

Both parts together, for the card `StandardModel.Model`.
-/

open TensorProduct MvPowerSeries Matrix MatrixGroups
open scoped Kronecker
open GaugeAlgebraRealization (covDerivIter symbols tower fieldStrength iteratedCovDerivAdjoint
  adjoin_symbols_eq_adjoin_covDerivIter)

/-! ## Part 1. The evaluation law -/

namespace LocalGaugeData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {G₀' : Type} [Group G₀'] {𝔤' : Type} [LieRing 𝔤'] [LieAlgebra ℝ 𝔤']
  {GJ' : Type} [Group GJ'] {𝔤J' : Type} [LieRing 𝔤J'] [LieAlgebra ℝ 𝔤J']
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {jets' : LocalGaugeData G₀' 𝔤' GJ' 𝔤J'}

/-! ### The law -/

/-- The evaluation law of a matrix representation: the matrix of a jet with trivial value has
  identity constant term. -/
def MatrixRep.EvalLaw {ι : Type} [Fintype ι] [DecidableEq ι] (R : MatrixRep jets ι) : Prop :=
  ∀ {W : GJ}, jets.eval W = 1 → (R.mat W).map (constantCoeff : SpaceTimeAlgebra → ℂ) = 1

/-- The evaluation law of a `U(1)` factor. -/
def U1Factor.EvalLaw (F : U1Factor jets) : Prop :=
  ∀ {W : GJ}, jets.eval W = 1 → constantCoeff (F.u W : SpaceTimeAlgebra) = 1

/-- The evaluation law of an `SU(n)` factor. -/
def SUFactor.EvalLaw {n : Type} [Fintype n] [DecidableEq n] (F : SUFactor jets n) : Prop :=
  ∀ {W : GJ}, jets.eval W = 1 → (F.u W).map (constantCoeff : SpaceTimeAlgebra → ℂ) = 1

/-- The evaluation law of a factor. -/
def Factor.EvalLaw : Factor jets → Prop
  | .U1 F => F.EvalLaw
  | .SU F => F.EvalLaw

/-- The evaluation law of a list of factors. -/
def Factors.EvalLaw : Factors jets → Prop
  | [] => True
  | F :: Fs => F.EvalLaw ∧ Factors.EvalLaw Fs

/-! ### Every construction of the table layer preserves it -/

lemma MatrixRep.trivial_evalLaw : (MatrixRep.trivial : MatrixRep jets (Fin 1)).EvalLaw := by
  intro W _
  show (1 : Matrix (Fin 1) (Fin 1) SpaceTimeAlgebra).map _ = 1
  exact Matrix.map_one _ (map_zero _) (map_one _)

lemma MatrixRep.kron_evalLaw {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂]
    [DecidableEq ι₂] {R₁ : MatrixRep jets ι₁} {R₂ : MatrixRep jets ι₂}
    (h₁ : R₁.EvalLaw) (h₂ : R₂.EvalLaw) : (R₁.kron R₂).EvalLaw := by
  intro W hW
  show (R₁.mat W ⊗ₖ R₂.mat W).map _ = 1
  have e₁ := h₁ hW
  have e₂ := h₂ hW
  rw [← Matrix.one_kronecker_one, ← e₁, ← e₂]
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [Matrix.kroneckerMap_apply, Matrix.map_apply]

lemma MatrixRep.conj_evalLaw {ι : Type} [Fintype ι] [DecidableEq ι] {R : MatrixRep jets ι}
    (h : R.EvalLaw) : R.conj.EvalLaw := by
  intro W hW
  show ((R.mat W).map (starRingEnd SpaceTimeAlgebra)).map _ = 1
  have e := h hW
  have key : ((R.mat W).map (starRingEnd SpaceTimeAlgebra)).map
      (constantCoeff : SpaceTimeAlgebra → ℂ)
      = ((R.mat W).map (constantCoeff : SpaceTimeAlgebra → ℂ)).map (starRingEnd ℂ) := by
    ext i j
    simp only [Matrix.map_apply]
    exact SpaceTimeAlgebra.constantCoeff_star _
  rw [key, e, Matrix.map_one _ (map_zero _) (map_one _)]

lemma constantCoeff_chargePow {n : ℤ} {u : unitary SpaceTimeAlgebra}
    (hu : constantCoeff (u : SpaceTimeAlgebra) = 1) :
    constantCoeff (MatterField.chargePow n u) = 1 := by
  have h1 : Units.map ((constantCoeff : SpaceTimeAlgebra →+* ℂ) : SpaceTimeAlgebra →* ℂ)
      (Unitary.toUnits u) = 1 := Units.ext hu
  have h2 := congrArg (fun x : ℂˣ => (x : ℂ))
    (map_zpow (Units.map ((constantCoeff : SpaceTimeAlgebra →+* ℂ) : SpaceTimeAlgebra →* ℂ))
      (Unitary.toUnits u) n)
  rw [h1, _root_.one_zpow, Units.val_one, Units.coe_map] at h2
  exact h2

lemma U1Factor.charge_evalLaw {ι : Type} [Fintype ι] [DecidableEq ι] {F : U1Factor jets}
    (hF : F.EvalLaw) (n : ℤ) {R : MatrixRep jets ι} (h : R.EvalLaw) : (F.charge n R).EvalLaw := by
  intro W hW
  show (MatterField.chargePow n (F.u W) • R.mat W).map _ = 1
  have e := h hW
  have c := constantCoeff_chargePow (n := n) (hF hW)
  rw [← e]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, c, one_mul]

lemma SUFactor.fund_evalLaw {n : Type} [Fintype n] [DecidableEq n] {F : SUFactor jets n}
    (hF : F.EvalLaw) : F.fund.EvalLaw := fun hW => hF hW

/-! ### Factors: pullback, and the canonical factors -/

lemma U1Factor.comap_evalLaw {F : U1Factor jets'} (hF : F.EvalLaw) (h : Hom jets jets') :
    (F.comap h).EvalLaw := fun {W} hW => hF (W := h.groupJ W) (by rw [h.eval_groupJ, hW, map_one])

lemma SUFactor.comap_evalLaw {n : Type} [Fintype n] [DecidableEq n] {F : SUFactor jets' n}
    (hF : F.EvalLaw) (h : Hom jets jets') : (F.comap h).EvalLaw :=
  fun {W} hW => hF (W := h.groupJ W) (by rw [h.eval_groupJ, hW, map_one])

lemma Factor.comap_evalLaw (h : Hom jets jets') :
    (F : Factor jets') → F.EvalLaw → (F.comap h).EvalLaw
  | .U1 _, hF => U1Factor.comap_evalLaw hF h
  | .SU _, hF => SUFactor.comap_evalLaw hF h

lemma Factors.comap_evalLaw (h : Hom jets jets') :
    (Γ : Factors jets') → Factors.EvalLaw Γ → Factors.EvalLaw (Factors.comap h Γ)
  | [], _ => True.intro
  | F :: Fs, hΓ => ⟨Factor.comap_evalLaw h F hΓ.1, Factors.comap_evalLaw h Fs hΓ.2⟩

lemma u1Factor_evalLaw : u1Factor.EvalLaw := by
  intro W hW
  have h : ((u1.eval W : U1) : ℂ) = 1 := by rw [hW]; rfl
  exact h

lemma MatrixJets.suFactor_evalLaw {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : MatrixJets κ G₀ 𝔤 GJ 𝔤J) : M.suFactor.EvalLaw := by
  intro W hW
  have h := M.toMat₀_eval W
  rw [show M.eval W = 1 from hW, map_one] at h
  exact h.symm

lemma FactorSpec.factor_evalLaw : (f : FactorSpec) → f.factor.EvalLaw
  | .U1 => u1Factor_evalLaw
  | .SU n => (suMatrixJets n).suFactor_evalLaw

/-- The canonical factors of a gauge group given as a list of factor symbols satisfy the law. -/
theorem Factors.factors_evalLaw : (Γ : List FactorSpec) → Factors.EvalLaw (Factors.factors Γ)
  | [] => True.intro
  | [f] => ⟨f.factor_evalLaw, True.intro⟩
  | f :: g :: gs =>
    ⟨Factor.comap_evalLaw Hom.fst _ f.factor_evalLaw,
      Factors.comap_evalLaw Hom.snd _ (Factors.factors_evalLaw (g :: gs))⟩

/-! ### The representation named by a charge tuple -/

lemma MatrixRep.kronDims_evalLaw {n : ℕ} {R₁ : MatrixRep jets (Fin n)} (h₁ : R₁.EvalLaw) :
    (ds : List ℕ) → (R₂ : MatrixRep jets (IdxOfDims ds)) → R₂.EvalLaw →
      (R₁.kronDims ds R₂).EvalLaw
  | [], _, _ => h₁
  | _ :: _, _, h₂ => MatrixRep.kron_evalLaw h₁ h₂

lemma SURep.repDims_evalLaw {n : ℕ} {F : SUFactor jets (Fin n)} (hF : F.EvalLaw) :
    (r : SURep) → (SURep.repDims F r).EvalLaw
  | .singlet => MatrixRep.trivial_evalLaw
  | .fund => SUFactor.fund_evalLaw hF
  | .antifund => MatrixRep.conj_evalLaw (SUFactor.fund_evalLaw hF)

theorem Charges.suRep_evalLaw :
    (Γ : Factors jets) → Factors.EvalLaw Γ → (c : Charges Γ) → (Charges.suRep Γ c).EvalLaw
  | [], _, _ => MatrixRep.trivial_evalLaw
  | [.U1 _], _, _ => MatrixRep.trivial_evalLaw
  | [.SU _], h, r => SURep.repDims_evalLaw h.1 r
  | .U1 _ :: g :: gs, h, c => Charges.suRep_evalLaw (g :: gs) h.2 c.2
  | .SU _ :: g :: gs, h, (.singlet, c) => Charges.suRep_evalLaw (g :: gs) h.2 c
  | .SU _ :: g :: gs, h, (.fund, c) =>
    MatrixRep.kronDims_evalLaw (SUFactor.fund_evalLaw h.1) _ _
      (Charges.suRep_evalLaw (g :: gs) h.2 c)
  | .SU _ :: g :: gs, h, (.antifund, c) =>
    MatrixRep.kronDims_evalLaw (MatrixRep.conj_evalLaw (SUFactor.fund_evalLaw h.1)) _ _
      (Charges.suRep_evalLaw (g :: gs) h.2 c)

theorem Charges.twist_evalLaw {ι : Type} [Fintype ι] [DecidableEq ι] :
    (Γ : Factors jets) → Factors.EvalLaw Γ → (c : Charges Γ) → (R : MatrixRep jets ι) →
      R.EvalLaw → (Charges.twist Γ c R).EvalLaw
  | [], _, _, _, hR => hR
  | [.U1 _], h, q, _, hR => U1Factor.charge_evalLaw h.1 q hR
  | [.SU _], _, _, _, hR => hR
  | .U1 _ :: g :: gs, h, c, R, hR =>
    U1Factor.charge_evalLaw h.1 c.1 (Charges.twist_evalLaw (g :: gs) h.2 c.2 R hR)
  | .SU _ :: g :: gs, h, c, R, hR => Charges.twist_evalLaw (g :: gs) h.2 c.2 R hR

/-- The representation named by any charge tuple satisfies the evaluation law. -/
theorem Charges.rep_evalLaw (Γ : Factors jets) (hΓ : Factors.EvalLaw Γ) (c : Charges Γ) :
    (Charges.rep Γ c).EvalLaw :=
  Charges.twist_evalLaw Γ hΓ c _ (Charges.suRep_evalLaw Γ hΓ c)

/-! ### Rows and tables -/

/-- Every row of a table over factors with the evaluation law satisfies
  `MatterField.PureJetsActTrivially`. -/
theorem MatterFieldData.toMatterField_pureJetsActTrivially {Γ : Factors jets}
    (hΓ : Factors.EvalLaw Γ) (M : MatterFieldData Γ) : M.toMatterField.PureJetsActTrivially :=
  MatrixRep.matterField_pureJetsActTrivially _ _ _ _ _ (fun hW => Charges.rep_evalLaw Γ hΓ M.charges hW)

/-- The field content of a table over factors with the evaluation law satisfies
  `GaugeFieldData.PureJetsActTrivially`. -/
theorem FieldData.toGaugeFieldData_pureJetsActTrivially [Module.Finite ℝ 𝔤] {Γ : Factors jets}
    (hΓ : Factors.EvalLaw Γ) {Fields : Type} [Fintype Fields] [DecidableEq Fields]
    (D : FieldData Γ Fields) : D.toGaugeFieldData.PureJetsActTrivially :=
  ⟨fun _ => MatterFieldData.toMatterField_pureJetsActTrivially hΓ _,
    fun _ => MatterFieldData.toMatterField_pureJetsActTrivially hΓ _⟩

end LocalGaugeData

/-- The Standard Model card satisfies both conditions of the covariant theory, with no
  model-specific proof. -/
theorem StandardModel.Model.fieldData_pureJetsActTrivially :
    StandardModel.Model.fieldData.PureJetsActTrivially :=
  LocalGaugeData.FieldData.toGaugeFieldData_pureJetsActTrivially
    (LocalGaugeData.Factors.factors_evalLaw StandardModel.Model.gauge) StandardModel.Model.table

theorem StandardModel.Model.fieldData_gaugeLorentzCompatible :
    StandardModel.Model.fieldData.GaugeLorentzCompatible :=
  LocalGaugeData.FieldData.toGaugeFieldData_gaugeLorentzCompatible StandardModel.Model.table

/-! ## Part 2. The covariant reduction theorem -/

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} {T : GaugeFieldData jets}

/-! ### Generation of `J(T)` by the derivative symbols -/

/-- A linear map out of `SpaceTimeDerivAlgebraℂ ⊗ W` whose values on the monomials
  `∂^s ⊗ w` lie in a submodule takes all its values there. -/
lemma mem_of_basis_tmul {W : Type} [AddCommMonoid W] [Module ℂ W] {N : Type} [AddCommMonoid N]
    [Module ℂ N] (Φ : SpaceTimeDerivAlgebraℂ ⊗[ℂ] W →ₗ[ℂ] N) (P : Submodule ℂ N)
    (h : ∀ s w, Φ (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] w) ∈ P)
    (x : SpaceTimeDerivAlgebraℂ ⊗[ℂ] W) : Φ x ∈ P := by
  induction x using TensorProduct.inductionOn with
  | tmul a w =>
    have ha : a ∈ Submodule.span ℂ (Set.range SpaceTimeDerivAlgebraℂ.basis) := by
      rw [SpaceTimeDerivAlgebraℂ.basis.span_eq]; exact Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem a ha => obtain ⟨s, rfl⟩ := ha; exact h s w
    | zero => rw [TensorProduct.zero_tmul, map_zero]; exact P.zero_mem
    | add a b _ _ ha hb => rw [TensorProduct.add_tmul, map_add]; exact P.add_mem ha hb
    | smul c a _ ha => rw [← TensorProduct.smul_tmul', map_smul]; exact P.smul_mem c ha
  | add x y hx hy => rw [map_add]; exact P.add_mem hx hy

/-- The generators of a fermionic species lie in any submodule containing its derivative
  symbols and their conjugates. -/
lemma ιFermion_mem_of_symbols (P : Submodule ℂ T.LocalFieldAlgebra) (i : T.FermionSpecies)
    (h₁ : ∀ s φ, T.fermionSymbol i s φ ∈ P) (h₂ : ∀ s φ, T.conjFermionSymbol i s φ ∈ P)
    (x : JetComponentSpace (T.fermion i)) : T.ιFermion i x ∈ P := by
  obtain ⟨a, b⟩ := x
  have hx : ((a, b) : JetComponentSpace (T.fermion i)) = (a, 0) + (0, b) := by simp
  have ha : T.fermionSymbolMap i a ∈ P := by
    refine mem_of_basis_tmul (T.fermionSymbolMap i) P ?_ a
    intro s φ
    exact h₁ s φ
  have hb : T.conjFermionSymbolMap i b ∈ P := by
    refine mem_of_basis_tmul (T.conjFermionSymbolMap i) P ?_ b
    intro s φ
    exact h₂ s φ
  rw [hx, map_add]
  exact P.add_mem ha hb

/-- The generators of a bosonic species lie in any submodule containing its derivative
  symbols and their conjugates. -/
lemma ιBoson_mem_of_symbols (P : Submodule ℂ T.LocalFieldAlgebra) (j : T.BosonSpecies)
    (h₁ : ∀ s φ, T.bosonSymbol j s φ ∈ P) (h₂ : ∀ s φ, T.conjBosonSymbol j s φ ∈ P)
    (y : JetComponentSpace (T.boson j)) : T.ιBoson j y ∈ P := by
  obtain ⟨a, b⟩ := y
  have hy : ((a, b) : JetComponentSpace (T.boson j)) = (a, 0) + (0, b) := by simp
  have ha : T.bosonSymbolMap j a ∈ P := by
    refine mem_of_basis_tmul (T.bosonSymbolMap j) P ?_ a
    intro s φ
    exact h₁ s φ
  have hb : T.conjBosonSymbolMap j b ∈ P := by
    refine mem_of_basis_tmul (T.conjBosonSymbolMap j) P ?_ b
    intro s φ
    exact h₂ s φ
  rw [hy, map_add]
  exact P.add_mem ha hb

/-- All fermionic generators lie in a submodule containing those of every species. -/
lemma ιFermionTotal_mem (P : Submodule ℂ T.LocalFieldAlgebra)
    (h : ∀ i x, T.ιFermion i x ∈ P) (v : T.FermionGenerators) : T.ιFermionTotal v ∈ P := by
  let g : T.FermionGenerators →ₗ[ℂ] P :=
    T.assembleFermion fun i => (T.ιFermion i).codRestrict P (h i)
  have hg : P.subtype ∘ₗ g = T.ιFermionTotal :=
    fermionGenerators_hom_ext fun i x => by
      show P.subtype (g (T.inclFermion i x)) = T.ιFermionTotal (T.inclFermion i x)
      rw [assembleFermion_inclFermion]
      rfl
  rw [← hg]
  exact (g v).2

/-- All bosonic generators lie in a submodule containing those of every species. -/
lemma ιBosonTotal_mem (P : Submodule ℂ T.LocalFieldAlgebra)
    (h : ∀ j y, T.ιBoson j y ∈ P) (v : T.BosonGenerators) : T.ιBosonTotal v ∈ P := by
  let g : T.BosonGenerators →ₗ[ℂ] P :=
    T.assembleBoson fun j => (T.ιBoson j).codRestrict P (h j)
  have hg : P.subtype ∘ₗ g = T.ιBosonTotal :=
    bosonGenerators_hom_ext fun j y => by
      show P.subtype (g (T.inclBoson j y)) = T.ιBosonTotal (T.inclBoson j y)
      rw [assembleBoson_inclBoson]
      rfl
  rw [← hg]
  exact (g v).2

/-- The connection generators are polynomials in the gauge-field symbols `∂_s A_μ^φ`. -/
lemma ιConnection_mem_adjoin (X : Set T.LocalFieldAlgebra)
    (hX : ∀ s μ φ, T.gaugeRealization.A s μ φ ∈ X) (v : GaugeBoson.JetComponentSpace 𝔤) :
    T.ιConnection v ∈ Algebra.adjoin ℂ X := by
  let Ψ : LocalGaugeFieldAlgebra 𝔤 →ₐ[ℝ] T.LocalFieldAlgebra :=
    (T.includeConnection.restrictScalars ℝ).comp Algebra.TensorProduct.includeRight
  have hle : (⊤ : Subalgebra ℝ (LocalGaugeFieldAlgebra 𝔤))
      ≤ ((Algebra.adjoin ℂ X).restrictScalars ℝ).comap Ψ := by
    rw [← LocalGaugeFieldAlgebra.adjoin_iteratedJetDeriv_eq_top]
    refine Algebra.adjoin_le ?_
    intro b hb
    simp only [Set.mem_iUnion, Set.mem_range] at hb
    obtain ⟨s, μ, φ, rfl⟩ := hb
    have : Ψ (LocalGaugeFieldAlgebra.iteratedJetDeriv 𝔤 s (LocalGaugeFieldAlgebra.ofA 𝔤 μ φ))
        = T.gaugeRealization.A s μ φ := by
      rw [gaugeRealization_A, LocalGaugeFieldAlgebra.gaugeField_eq_one_tmul_derivA]
      rfl
    show Ψ (LocalGaugeFieldAlgebra.iteratedJetDeriv 𝔤 s (LocalGaugeFieldAlgebra.ofA 𝔤 μ φ))
      ∈ Algebra.adjoin ℂ X
    rw [this]
    exact Algebra.subset_adjoin (hX s μ φ)
  exact hle (Algebra.mem_top (x := SymmetricAlgebra.ι ℝ (GaugeBoson.JetComponentSpace 𝔤) v))

/-! ### The matter towers -/

variable (T) in
/-- The covariant matter towers of every species, unconjugated and conjugate. -/
def matterTowers : Set T.LocalFieldAlgebra :=
  (⋃ i, ⋃ n : ℕ, ⋃ l : Fin n → (Fin 1 ⊕ Fin 3),
      Set.range (T.covDerivFermion i l) ∪ Set.range (T.covDerivConjFermion i l))
    ∪ (⋃ j, ⋃ n : ℕ, ⋃ l : Fin n → (Fin 1 ⊕ Fin 3),
      Set.range (T.covDerivBoson j l) ∪ Set.range (T.covDerivConjBoson j l))

lemma covDerivFermion_mem_matterTowers (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.FermionValue i)) :
    T.covDerivFermion i l φ ∈ T.matterTowers :=
  Or.inl (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l, Or.inl ⟨φ, rfl⟩⟩⟩⟩)

lemma covDerivConjFermion_mem_matterTowers (i : T.FermionSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.FermionValue i))) :
    T.covDerivConjFermion i l φ ∈ T.matterTowers :=
  Or.inl (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l, Or.inr ⟨φ, rfl⟩⟩⟩⟩)

lemma covDerivBoson_mem_matterTowers (j : T.BosonSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (T.BosonValue j)) :
    T.covDerivBoson j l φ ∈ T.matterTowers :=
  Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l, Or.inl ⟨φ, rfl⟩⟩⟩⟩)

lemma covDerivConjBoson_mem_matterTowers (j : T.BosonSpecies) {n : ℕ}
    (l : Fin n → (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ (ConjModule (T.BosonValue j))) :
    T.covDerivConjBoson j l φ ∈ T.matterTowers :=
  Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨l, Or.inr ⟨φ, rfl⟩⟩⟩⟩)

/-- A derivative symbol of a matter family is a polynomial in the gauge-field symbols and the
  covariant tower of the family. -/
lemma symbol_mem_adjoin {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V)
    (F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] T.LocalFieldAlgebra)
    (hF : ∀ (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) φ,
      covDerivIter T.gaugeRealization.A act F n l 0 φ ∈ T.matterTowers)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    F s φ ∈ Algebra.adjoin ℂ (symbols T.gaugeRealization.A ∪ T.matterTowers) := by
  refine Algebra.adjoin_mono ?_
    ((adjoin_symbols_eq_adjoin_covDerivIter (A := T.gaugeRealization.A) act F).le
      (Algebra.subset_adjoin (Or.inr ⟨s, φ, rfl⟩)))
  rintro b (⟨s, μ, ψ, rfl⟩ | ⟨n, l, φ, rfl⟩)
  exacts [Or.inl ⟨s, μ, ψ, rfl⟩, Or.inr (hF n l φ)]

/-- **The covariant towers and the gauge-field symbols generate `J(T)`.** -/
theorem adjoin_symbols_union_matterTowers_eq_top :
    Algebra.adjoin ℂ (symbols T.gaugeRealization.A ∪ T.matterTowers) = ⊤ := by
  rw [eq_top_iff, ← T.adjoin_generators_eq_top]
  refine Algebra.adjoin_le ?_
  set P := Algebra.adjoin ℂ (symbols T.gaugeRealization.A ∪ T.matterTowers) with hP
  rintro b ((⟨v, rfl⟩ | ⟨v, rfl⟩) | ⟨v, rfl⟩)
  · exact ιFermionTotal_mem (Subalgebra.toSubmodule P) (fun i x =>
      ιFermion_mem_of_symbols (Subalgebra.toSubmodule P) i
        (fun s φ => symbol_mem_adjoin _ _ (fun n l φ => covDerivFermion_mem_matterTowers i l φ) s φ)
        (fun s φ => symbol_mem_adjoin _ _
          (fun n l φ => covDerivConjFermion_mem_matterTowers i l φ) s φ) x) v
  · exact ιBosonTotal_mem (Subalgebra.toSubmodule P) (fun j y =>
      ιBoson_mem_of_symbols (Subalgebra.toSubmodule P) j
        (fun s φ => symbol_mem_adjoin _ _ (fun n l φ => covDerivBoson_mem_matterTowers j l φ) s φ)
        (fun s φ => symbol_mem_adjoin _ _
          (fun n l φ => covDerivConjBoson_mem_matterTowers j l φ) s φ) y) v
  · exact ιConnection_mem_adjoin _ (fun s μ φ => Or.inl ⟨s, μ, φ, rfl⟩) v

/-! ### The reduction theorem -/

/-- Pure jets fix the matter towers, when they act trivially on every species at the base
  point. -/
lemma repJet_eq_self_of_mem_matterTowers (hP : T.PureJetsActTrivially)
    {y : T.LocalFieldAlgebra} (hy : y ∈ T.matterTowers) (U : jets.truncationKer 0) :
    T.repJet U.1 y = y := by
  have hU : jets.eval U.1 = 1 := jets.mem_truncationKer_zero_iff.mp U.2
  have h1 : ∀ z : T.LocalFieldAlgebra, T.repJet (jets.ofConstant (jets.eval U.1)) z = z := by
    intro z
    rw [hU, map_one, map_one]
    rfl
  simp only [matterTowers, Set.mem_union, Set.mem_iUnion, Set.mem_range] at hy
  rcases hy with ⟨i, n, l, ⟨φ, rfl⟩ | ⟨φ, rfl⟩⟩ | ⟨j, n, l, ⟨φ, rfl⟩ | ⟨φ, rfl⟩⟩
  · rw [repJet_covDerivFermion_ofConstant_eval U.1 i (hP.1 i) l φ, h1]
  · rw [repJet_covDerivConjFermion_ofConstant_eval U.1 i (hP.1 i) l φ, h1]
  · rw [repJet_covDerivBoson_ofConstant_eval U.1 j (hP.2 j) l φ, h1]
  · rw [repJet_covDerivConjBoson_ofConstant_eval U.1 j (hP.2 j) l φ, h1]

/-- **The covariant reduction theorem.** For free gauge data and species on which pure jets
  act trivially at the base point, every element of the local field algebra fixed by all
  jets of gauge transformations lies in the covariant field algebra: it is a polynomial in
  the covariant derivatives of the field strength and of the matter fields. -/
theorem mem_localCovFieldAlgebra_of_gaugeInvariant [jets.Free] (hP : T.PureJetsActTrivially)
    {x : T.LocalFieldAlgebra} (hinv : ∀ U : GJ, T.repJet U x = x) :
    x ∈ T.LocalCovFieldAlgebra := by
  have hx : x ∈ Algebra.adjoin ℂ (symbols T.gaugeRealization.A ∪ T.matterTowers) := by
    rw [adjoin_symbols_union_matterTowers_eq_top]
    exact Algebra.mem_top
  have key := T.gaugeRealization.invariant_mem_adjoin_fieldStrength T.matterTowers
    (fun p μ φ y _ => (includeConnection_commute _ y).symm)
    (fun y hy U => repJet_eq_self_of_mem_matterTowers hP hy U) hx hinv
  refine Algebra.adjoin_mono ?_ key
  rintro b (⟨l, ν, lam, φ, rfl⟩ | hb)
  · have hm : T.covDerivFieldStrength l ν lam φ ∈ T.covGenerators :=
      Or.inl (Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨ν, Set.mem_iUnion.mpr ⟨lam, φ, rfl⟩⟩⟩)
    exact (congrArg (· ∈ T.covGenerators)
      (covDerivFieldStrength_eq_iteratedCovDerivAdjoint (T := T) l ν lam φ)).mp hm
  · exact Or.inr hb

/-- **Gauge invariance is covariance plus global invariance.** An element of `J(T)` is
  fixed by all jets of gauge transformations exactly when it lies in the covariant field
  algebra and is fixed by the constant jets. -/
theorem forall_repJet_eq_iff [jets.Free] (hP : T.PureJetsActTrivially) (x : T.LocalFieldAlgebra) :
    (∀ U : GJ, T.repJet U x = x)
      ↔ x ∈ T.LocalCovFieldAlgebra ∧ ∀ g : G₀, T.repJet (jets.ofConstant g) x = x := by
  refine ⟨fun h => ⟨mem_localCovFieldAlgebra_of_gaugeInvariant hP h, fun g => h _⟩, ?_⟩
  rintro ⟨hx, hg⟩ U
  rw [LocalCovFieldAlgebra.repJet_eq_ofConstant_eval_of_mem hP U hx]
  exact hg _

/-- The gauge invariants of `J(T)` lie in the covariant field algebra. -/
theorem gaugeInvariants_le_localCovFieldAlgebra [jets.Free] (hP : T.PureJetsActTrivially) :
    T.gaugeInvariants ≤ Subalgebra.toSubmodule T.LocalCovFieldAlgebra :=
  fun _ hx => mem_localCovFieldAlgebra_of_gaugeInvariant hP (T.mem_gaugeInvariants_iff.mp hx)

end GaugeFieldData

/-! ## Part 3. The Standard Model card -/

namespace StandardModel.Model

/-- **On the Standard Model card, jet-gauge invariance is covariance together with global
  gauge invariance.** Nothing here is specific to the Standard Model: the gauge data of a
  list of factors is free, and the rows of a table satisfy the evaluation law. -/
theorem forall_repJet_eq_iff (x : fieldData.LocalFieldAlgebra) :
    (∀ U, fieldData.repJet U x = x)
      ↔ x ∈ fieldData.LocalCovFieldAlgebra
        ∧ ∀ g, fieldData.repJet (gaugeData.ofConstant g) x = x :=
  GaugeFieldData.forall_repJet_eq_iff fieldData_pureJetsActTrivially x

end StandardModel.Model

#print axioms StandardModel.Model.fieldData_pureJetsActTrivially
#print axioms GaugeFieldData.mem_localCovFieldAlgebra_of_gaugeInvariant
#print axioms StandardModel.Model.forall_repJet_eq_iff
