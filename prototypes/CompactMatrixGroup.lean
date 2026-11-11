import Mathlib

/-!
# Prototype: a compact matrix group is a closed subgroup of `U(κ)`; its Lie algebra is derived

Compiled against Mathlib v4.35.0, the revision physlib pins, with Lean v4.35.0, by
`lake env lean CompactMatrixGroup.lean` from a physlib checkout. It imports Mathlib only. Not
part of Physlib; a design check, written for the review of physlib PR 2061 without using the
code of that PR.

The only datum is the closed subgroup. The Lie algebra is *defined* as the set of generators
of one-parameter subgroups, and that this set is a real subspace is a theorem (the Lie
product formula, which for unitary matrices is short because the operator norm is invariant
under multiplication by unitaries).

## Contents

- Generators of one-parameter subgroups (`IsGenerator`); they are anti-hermitian.
- The Lie product formula for a closed group of unitary matrices (`IsGenerator.exp_add_mem`),
  so the generators are closed under addition (`IsGenerator.add`).
- The proposed definition: `CompactMatrixGroup` and `lieAlgebra`.
- The form used in physlib PR 2061: `lieAlgebraOfIsClosed`, and `existsUnique_lieAlgebra`.
- Two groups: `unitary`, with its Lie algebra, and `specialUnitary`.
- Compactness: `isCompact_unitaryGroup`, and every compact matrix group is compact.
-/

open Matrix NormedSpace Filter Topology

namespace ClosedUnitaryGroup

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- `X` generates a one-parameter subgroup of `G`: `exp (t X) ∈ G` for every real `t`. -/
def IsGenerator (G : Subgroup (unitaryGroup κ ℂ)) (X : Matrix κ κ ℂ) : Prop :=
  ∀ t : ℝ, ∃ g ∈ G, (g : Matrix κ κ ℂ) = exp (t • X)

theorem isGenerator_zero (G : Subgroup (unitaryGroup κ ℂ)) : IsGenerator G 0 := fun t =>
  ⟨1, G.one_mem, by rw [smul_zero, NormedSpace.exp_zero]; rfl⟩

theorem IsGenerator.smul {G : Subgroup (unitaryGroup κ ℂ)} {X : Matrix κ κ ℂ}
    (hX : IsGenerator G X) (r : ℝ) : IsGenerator G (r • X) := fun t => by
  obtain ⟨g, hg, h⟩ := hX (t * r)
  exact ⟨g, hg, by rw [h, mul_smul]⟩

/-- The exponential of an anti-hermitian matrix is unitary. -/
theorem exp_mem_unitaryGroup {Z : Matrix κ κ ℂ} (hZ : Zᴴ = -Z) : exp Z ∈ unitaryGroup κ ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hZ,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel,
    NormedSpace.exp_zero]

/-- A generator of a one-parameter subgroup of unitary matrices is anti-hermitian. -/
theorem IsGenerator.conjTranspose_eq_neg {G : Subgroup (unitaryGroup κ ℂ)} {X : Matrix κ κ ℂ}
    (hX : IsGenerator G X) : Xᴴ = -X := by
  let _ : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
  have hφ : (fun t : ℝ => exp (t • Xᴴ) * exp (t • X)) = fun _ => (1 : Matrix κ κ ℂ) := by
    funext t
    obtain ⟨g, -, hg⟩ := hX t
    have h1 : star (g : Matrix κ κ ℂ) * (g : Matrix κ κ ℂ) = 1 := mem_unitaryGroup_iff'.mp g.2
    rw [hg, star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul,
      star_trivial] at h1
    exact h1
  have h : HasDerivAt (fun t : ℝ => exp (t • Xᴴ) * exp (t • X))
      (exp ((0 : ℝ) • Xᴴ) * Xᴴ * exp ((0 : ℝ) • X)
        + exp ((0 : ℝ) • Xᴴ) * (exp ((0 : ℝ) • X) * X)) 0 :=
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᴴ 0).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
  rw [hφ] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) (1 : Matrix κ κ ℂ))
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h0
  exact eq_neg_of_add_eq_zero_left h0

omit [Fintype κ] [DecidableEq κ] in
theorem ofReal_smul_eq (s : ℝ) (X : Matrix κ κ ℂ) : (s : ℂ) • X = s • X := by
  ext i j
  simp [Complex.real_smul]

section Trotter

open scoped Matrix.Norms.L2Operator

/-- Powers of unitary matrices: the operator norm is invariant under multiplication by
  unitaries, so the telescoping sum has no growth. -/
theorem norm_pow_sub_pow_le {A B : Matrix κ κ ℂ} (hA : A ∈ unitaryGroup κ ℂ)
    (hB : B ∈ unitaryGroup κ ℂ) (n : ℕ) : ‖A ^ n - B ^ n‖ ≤ n * ‖A - B‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : A ^ (n + 1) - B ^ (n + 1) = A * (A ^ n - B ^ n) + (A - B) * B ^ n := by
      rw [pow_succ', pow_succ']
      noncomm_ring
    have e1 : ‖A * (A ^ n - B ^ n)‖ = ‖A ^ n - B ^ n‖ :=
      CStarRing.norm_coe_unitary_mul ⟨A, hA⟩ _
    have e2 : ‖(A - B) * B ^ n‖ = ‖A - B‖ :=
      CStarRing.norm_mul_coe_unitary _ ⟨B ^ n, pow_mem hB n⟩
    calc ‖A ^ (n + 1) - B ^ (n + 1)‖
        = ‖A * (A ^ n - B ^ n) + (A - B) * B ^ n‖ := by rw [h]
      _ ≤ ‖A * (A ^ n - B ^ n)‖ + ‖(A - B) * B ^ n‖ := norm_add_le _ _
      _ = ‖A ^ n - B ^ n‖ + ‖A - B‖ := by rw [e1, e2]
      _ ≤ n * ‖A - B‖ + ‖A - B‖ := by gcongr
      _ = ((n + 1 : ℕ) : ℝ) * ‖A - B‖ := by push_cast; ring

/-- The error of one Trotter step is of second order. -/
theorem tendsto_trotter_error (X Y : Matrix κ κ ℂ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      ‖exp ((1 / ((n : ℝ) + 1)) • X) * exp ((1 / ((n : ℝ) + 1)) • Y)
        - exp ((1 / ((n : ℝ) + 1)) • (X + Y))‖) atTop (𝓝 0) := by
  have hF := ((hasDerivAt_exp_smul_const (𝕂 := ℂ) X 0).mul
    (hasDerivAt_exp_smul_const (𝕂 := ℂ) Y 0)).sub
    (hasDerivAt_exp_smul_const (𝕂 := ℂ) (X + Y) 0)
  have hu : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have := (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [Function.comp_def] using this
    · exact Complex.ofReal_ne_zero.mpr (Nat.one_div_pos_of_nat (α := ℝ)).ne'
  have h := (hF.tendsto_slope_zero.comp hu).norm
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, sub_self, norm_zero] at h
  refine h.congr fun n => ?_
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simp only [Function.comp_apply, Pi.sub_apply, Pi.mul_apply, zero_add, zero_smul,
    NormedSpace.exp_zero, mul_one, sub_self, sub_zero, norm_smul, norm_inv, Complex.norm_real,
    one_div, inv_inv, Real.norm_of_nonneg hpos.le, ofReal_smul_eq]

end Trotter

section Closed

open scoped Matrix.Norms.L2Operator

/-- **The Lie product formula for a closed group of unitary matrices**: if `exp (t X)` and
  `exp (t Y)` lie in the group for every `t`, so does `exp (X + Y)`. -/
theorem IsGenerator.exp_add_mem {G : Subgroup (unitaryGroup κ ℂ)}
    (hG : IsClosed (G : Set (unitaryGroup κ ℂ))) {X Y : Matrix κ κ ℂ}
    (hX : IsGenerator G X) (hY : IsGenerator G Y) :
    ∃ g ∈ G, (g : Matrix κ κ ℂ) = exp (X + Y) := by
  have hXY : (X + Y)ᴴ = -(X + Y) := by
    rw [conjTranspose_add, hX.conjTranspose_eq_neg, hY.conjTranspose_eq_neg, neg_add]
  let u : unitaryGroup κ ℂ := ⟨exp (X + Y), exp_mem_unitaryGroup hXY⟩
  choose gx hgx hgx' using fun n : ℕ => hX (1 / ((n : ℝ) + 1))
  choose gy hgy hgy' using fun n : ℕ => hY (1 / ((n : ℝ) + 1))
  let c : ℕ → unitaryGroup κ ℂ := fun n => (gx n * gy n) ^ (n + 1)
  have hc : ∀ n, c n ∈ G := fun n => G.pow_mem (G.mul_mem (hgx n) (hgy n)) _
  suffices h : Tendsto c atTop (𝓝 u) from
    ⟨u, hG.mem_of_tendsto h (Eventually.of_forall hc), rfl⟩
  rw [tendsto_subtype_rng, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (tendsto_trotter_error X Y)
  have hb : exp ((1 / ((n : ℝ) + 1)) • (X + Y)) ∈ unitaryGroup κ ℂ :=
    exp_mem_unitaryGroup (by rw [conjTranspose_smul, star_trivial, hXY, smul_neg])
  have ha : exp ((1 / ((n : ℝ) + 1)) • X) * exp ((1 / ((n : ℝ) + 1)) • Y) ∈ unitaryGroup κ ℂ := by
    rw [← hgx' n, ← hgy' n]
    exact mul_mem (gx n).2 (gy n).2
  have hpow : exp ((1 / ((n : ℝ) + 1)) • (X + Y)) ^ (n + 1) = exp (X + Y) := by
    rw [← Matrix.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_add_one,
      mul_one_div_cancel (Nat.cast_add_one_ne_zero n), one_smul]
  have hcn : ((c n : unitaryGroup κ ℂ) : Matrix κ κ ℂ)
      = (exp ((1 / ((n : ℝ) + 1)) • X) * exp ((1 / ((n : ℝ) + 1)) • Y)) ^ (n + 1) := by
    rw [← hgx' n, ← hgy' n]
    rfl
  calc ‖((c n : unitaryGroup κ ℂ) : Matrix κ κ ℂ) - (u : Matrix κ κ ℂ)‖
      = ‖(exp ((1 / ((n : ℝ) + 1)) • X) * exp ((1 / ((n : ℝ) + 1)) • Y)) ^ (n + 1)
          - exp ((1 / ((n : ℝ) + 1)) • (X + Y)) ^ (n + 1)‖ := by rw [hcn, hpow]
    _ ≤ ((n + 1 : ℕ) : ℝ) * ‖exp ((1 / ((n : ℝ) + 1)) • X) * exp ((1 / ((n : ℝ) + 1)) • Y)
          - exp ((1 / ((n : ℝ) + 1)) • (X + Y))‖ := norm_pow_sub_pow_le ha hb (n + 1)
    _ = ((n : ℝ) + 1) * ‖exp ((1 / ((n : ℝ) + 1)) • X) * exp ((1 / ((n : ℝ) + 1)) • Y)
          - exp ((1 / ((n : ℝ) + 1)) • (X + Y))‖ := by rw [Nat.cast_add_one]

end Closed

/-- The generators of the one-parameter subgroups of a closed group of unitary matrices are
  closed under addition. -/
theorem IsGenerator.add {G : Subgroup (unitaryGroup κ ℂ)}
    (hG : IsClosed (G : Set (unitaryGroup κ ℂ))) {X Y : Matrix κ κ ℂ}
    (hX : IsGenerator G X) (hY : IsGenerator G Y) : IsGenerator G (X + Y) := fun t => by
  rw [smul_add]
  exact (hX.smul t).exp_add_mem hG (hY.smul t)

/-!
## The proposed definition
-/

/-- **A compact matrix group**: a closed subgroup of the unitary group `U(κ)`. Nothing else
  is data. -/
abbrev CompactMatrixGroup (κ : Type) [Fintype κ] [DecidableEq κ] : Type :=
  ClosedSubgroup (unitaryGroup κ ℂ)

/-- **The Lie algebra of a compact matrix group**, derived from the group: the matrices `X`
  whose one-parameter subgroup `t ↦ exp (t X)` lies in the group. -/
def lieAlgebra (G : CompactMatrixGroup κ) : Submodule ℝ (Matrix κ κ ℂ) where
  carrier := {X | IsGenerator G.toSubgroup X}
  add_mem' hX hY := IsGenerator.add G.isClosed' hX hY
  zero_mem' := isGenerator_zero _
  smul_mem' r _ hX := IsGenerator.smul hX r

/-- What is a field of the structure in physlib PR 2061 holds here by definition. -/
theorem mem_lieAlgebra_iff {G : CompactMatrixGroup κ} {X : Matrix κ κ ℂ} :
    X ∈ lieAlgebra G ↔ ∀ t : ℝ, ∃ g ∈ G.toSubgroup, (g : Matrix κ κ ℂ) = exp (t • X) :=
  Iff.rfl

/-!
## The form used in physlib PR 2061

There the structure has two more fields: a subspace `lieAlgebra`, and the statement
`mem_lieAlgebra_iff` that its elements are the `X` with
`exp (t • X) ∈ Set.range fun g : group => (g.1.1 : Matrix κ κ ℂ)` for every real `t`. Both can
be derived from the closed subgroup.
-/

/-- The condition in the field `mem_lieAlgebra_iff` of PR 2061 is `IsGenerator`. -/
theorem isGenerator_iff_forall_mem_range {G : Subgroup (unitaryGroup κ ℂ)} {X : Matrix κ κ ℂ} :
    IsGenerator G X ↔
      ∀ t : ℝ, exp (t • X) ∈ Set.range fun g : G => (g.1.1 : Matrix κ κ ℂ) :=
  forall_congr' fun _ => ⟨fun ⟨g, hg, h⟩ => ⟨⟨g, hg⟩, h⟩, fun ⟨g, h⟩ => ⟨g.1, g.2, h⟩⟩

/-- The Lie algebra of a subgroup of `U(κ)` with a closedness hypothesis, with membership
  stated as in PR 2061. With it the two fields of that structure can be replaced by the
  definition `lieAlgebra := lieAlgebraOfIsClosed G.group G.isClosed` and a lemma
  `mem_lieAlgebra_iff` with the statement of the field, proved by `Iff.rfl`. -/
def lieAlgebraOfIsClosed (G : Subgroup (unitaryGroup κ ℂ))
    (hG : IsClosed (G : Set (unitaryGroup κ ℂ))) : Submodule ℝ (Matrix κ κ ℂ) where
  carrier := {X | ∀ t : ℝ, exp (t • X) ∈ Set.range fun g : G => (g.1.1 : Matrix κ κ ℂ)}
  add_mem' hX hY := isGenerator_iff_forall_mem_range.mp
    ((isGenerator_iff_forall_mem_range.mpr hX).add hG (isGenerator_iff_forall_mem_range.mpr hY))
  zero_mem' := isGenerator_iff_forall_mem_range.mp (isGenerator_zero G)
  smul_mem' r _ hX := isGenerator_iff_forall_mem_range.mp
    ((isGenerator_iff_forall_mem_range.mpr hX).smul r)

theorem mem_lieAlgebraOfIsClosed_iff {G : Subgroup (unitaryGroup κ ℂ)}
    {hG : IsClosed (G : Set (unitaryGroup κ ℂ))} {X : Matrix κ κ ℂ} :
    X ∈ lieAlgebraOfIsClosed G hG ↔
      ∀ t : ℝ, exp (t • X) ∈ Set.range fun g : G => (g.1.1 : Matrix κ κ ℂ) :=
  Iff.rfl

/-- It is the Lie algebra of the closed subgroup. -/
theorem lieAlgebraOfIsClosed_eq (G : Subgroup (unitaryGroup κ ℂ))
    (hG : IsClosed (G : Set (unitaryGroup κ ℂ))) :
    lieAlgebraOfIsClosed G hG = lieAlgebra ⟨G, hG⟩ :=
  Submodule.ext fun _ => isGenerator_iff_forall_mem_range.symm

/-- Every closed subgroup of `U(κ)` has exactly one Lie algebra in the sense of the fields
  `lieAlgebra` and `mem_lieAlgebra_iff` of PR 2061: those two fields carry no information. -/
theorem existsUnique_lieAlgebra (G : Subgroup (unitaryGroup κ ℂ))
    (hG : IsClosed (G : Set (unitaryGroup κ ℂ))) :
    ∃! 𝔤 : Submodule ℝ (Matrix κ κ ℂ), ∀ X, X ∈ 𝔤 ↔
      ∀ t : ℝ, exp (t • X) ∈ Set.range fun g : G => (g.1.1 : Matrix κ κ ℂ) :=
  ⟨lieAlgebraOfIsClosed G hG, fun _ => Iff.rfl, fun _ h𝔤 => Submodule.ext fun X => h𝔤 X⟩

/-!
## Two groups, with no Lie theory needed to write them down
-/

/-- The unitary group `U(κ)` as a compact matrix group. -/
def unitary : CompactMatrixGroup κ := ⟨⊤, isClosed_univ⟩

/-- The Lie algebra of `U(κ)`: the anti-hermitian matrices. -/
theorem mem_lieAlgebra_unitary_iff {X : Matrix κ κ ℂ} :
    X ∈ lieAlgebra (unitary (κ := κ)) ↔ Xᴴ = -X :=
  ⟨fun h => IsGenerator.conjTranspose_eq_neg h, fun h t =>
    ⟨⟨exp (t • X), exp_mem_unitaryGroup (by rw [conjTranspose_smul, star_trivial, h, smul_neg])⟩,
      Subgroup.mem_top _, rfl⟩⟩

/-- The special unitary group `SU(κ)` as a compact matrix group: unitary matrices of
  determinant one. Closedness is continuity of the determinant. -/
def specialUnitary : CompactMatrixGroup κ where
  toSubgroup := (Matrix.detMonoidHom.comp (unitaryGroup κ ℂ).subtype).ker
  isClosed' :=
    (isClosed_singleton (x := (1 : ℂ))).preimage
      (continuous_subtype_val.matrix_det : Continuous fun u : unitaryGroup κ ℂ =>
        (u : Matrix κ κ ℂ).det)

theorem mem_specialUnitary_iff {u : unitaryGroup κ ℂ} :
    u ∈ (specialUnitary (κ := κ)).toSubgroup ↔ (u : Matrix κ κ ℂ).det = 1 := Iff.rfl

/-!
## Compactness

"Compact" is a theorem, not part of the data: the unitary group is compact, and a closed
subgroup of a compact group is compact (an instance of Mathlib's `ClosedSubgroup`).
-/

/-- The unitary group is compact: it is closed, and its entries are bounded by one. -/
theorem isCompact_unitaryGroup : IsCompact (unitaryGroup κ ℂ : Set (Matrix κ κ ℂ)) := by
  have hK : IsCompact (X := Matrix κ κ ℂ) (Set.pi Set.univ fun _ : κ =>
      Set.pi Set.univ fun _ : κ => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hK.of_isClosed_subset (isClosed_unitary (R := Matrix κ κ ℂ)) fun U hU i _ j _ => ?_
  rw [mem_closedBall_zero_iff]
  exact entry_norm_bound_of_unitary hU i j

instance : CompactSpace (unitaryGroup κ ℂ) :=
  isCompact_iff_compactSpace.mp isCompact_unitaryGroup

/-- A compact matrix group is compact. -/
example (G : CompactMatrixGroup κ) : CompactSpace G := inferInstance

end ClosedUnitaryGroup

#print axioms ClosedUnitaryGroup.lieAlgebra
#print axioms ClosedUnitaryGroup.existsUnique_lieAlgebra
#print axioms ClosedUnitaryGroup.lieAlgebraOfIsClosed
#print axioms ClosedUnitaryGroup.mem_lieAlgebra_unitary_iff
#print axioms ClosedUnitaryGroup.specialUnitary
#print axioms ClosedUnitaryGroup.isCompact_unitaryGroup
