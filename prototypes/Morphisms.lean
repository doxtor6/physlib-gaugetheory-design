import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalField.Realization
import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalField.MassWeight

/-!
# Prototype: morphisms of field data and the functoriality of the local field algebra

Compiled against the branch of physlib PR #2011 (commit `800e1cf6`), Lean v4.35.0, with
`lake env lean Morphisms.lean`. Not part of Physlib; a design check.

The local field algebra `J(T)` depends on the field datum `T` only through its two generator
spaces, with the jet gauge action, the Lorentz action and the mass-weight scaling on them.

* `GenHom T T'` : a map of generator spaces intertwining the three. It induces an algebra map
  `J(T) → J(T')` (`GenHom.toAlgHom`), which is a realization of `T` in `J(T')`
  (`GenHom.toRealization`), respects the mass-weight scaling, and is functorial
  (`GenHom.toAlgHom_id`, `GenHom.toAlgHom_comp`).
* `GenEquiv T T'` : an equivalence of generator spaces. It induces `J(T) ≃ₐ J(T')` and carries
  the gauge and Lorentz invariants of mass weight at most `w` of `T` onto those of `T'`
  (`GenEquiv.invariantsLE_map`).
* `SpeciesEquiv T T'` : a bijection of species with isomorphisms of their matter fields. It is
  an equivalence of generator spaces (`SpeciesEquiv.toGenEquiv`); the direct sums are
  reindexed with `DirectSum.lequivCongrLeft`, so no transport along equalities of species
  appears. Hence two descriptions of a theory differing by a renaming of the species and by
  isomorphisms of their matter fields have the same invariants
  (`SpeciesEquiv.invariantsLE_map`).
* `SpeciesHom T T'` : every species of `T'` receives an intertwiner from one species of `T`,
  not necessarily invertible. It induces a map of generator spaces in the opposite direction
  (`SpeciesHom.toGenHom : GenHom T' T`), the symbols being covectors.
-/

open TensorProduct Matrix MatrixGroups
open scoped DirectSum

/-- A linear equivalence of direct sums from a bijection of the index types and a family of
  linear equivalences of the summands. -/
noncomputable def DirectSum.lequivOfEquiv {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) {A : ι → Type} {B : κ → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    [∀ k, AddCommGroup (B k)] [∀ k, Module ℂ (B k)] (f : ∀ i, A i ≃ₗ[ℂ] B (e i)) :
    (⨁ i, A i) ≃ₗ[ℂ] (⨁ k, B k) :=
  (DFinsupp.mapRange.linearEquiv f).trans (DirectSum.lequivCongrLeft ℂ e.symm).symm

lemma DirectSum.lequivOfEquiv_lof {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) {A : ι → Type} {B : κ → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    [∀ k, AddCommGroup (B k)] [∀ k, Module ℂ (B k)] (f : ∀ i, A i ≃ₗ[ℂ] B (e i))
    (i : ι) (a : A i) :
    DirectSum.lequivOfEquiv e f (DirectSum.lof ℂ ι A i a) = DirectSum.lof ℂ κ B (e i) (f i a) := by
  rw [DirectSum.lequivOfEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  refine DFinsupp.ext fun k => ?_
  rw [DirectSum.lequivCongrLeft_apply]
  show (DFinsupp.mapRange (fun i => f i) (fun i => map_zero (f i)) (DFinsupp.single i a)) k
      = (DFinsupp.single (e i) (f i a) : Π₀ k, B k) (e k)
  rw [DFinsupp.mapRange_single]
  by_cases h : i = k
  · subst h
    simp
  · rw [DFinsupp.single_eq_of_ne (Ne.symm h), DFinsupp.single_eq_of_ne (fun h' => h (e.injective h').symm)]


namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

/-! ### The actions of `J(T)` on all the generators of a statistic at once -/

section Total

variable {T : GaugeFieldData jets}

lemma repJet_ιFermionTotal (U : GJ) (w : T.FermionGenerators) :
    T.repJet U (T.ιFermionTotal w) = T.ιFermionTotal (T.repJetFermion U w) :=
  LinearMap.congr_fun (fermionGenerators_hom_ext
    (F := (T.repJet U) ∘ₗ T.ιFermionTotal) (F' := T.ιFermionTotal ∘ₗ T.repJetFermion U)
    fun i x => by
      simp only [LinearMap.comp_apply, repJetFermion_inclFermion, ← ιFermion_apply,
        repJet_ιFermion]) w

lemma repJet_ιBosonTotal (U : GJ) (w : T.BosonGenerators) :
    T.repJet U (T.ιBosonTotal w) = T.ιBosonTotal (T.repJetBoson U w) :=
  LinearMap.congr_fun (bosonGenerators_hom_ext
    (F := (T.repJet U) ∘ₗ T.ιBosonTotal) (F' := T.ιBosonTotal ∘ₗ T.repJetBoson U)
    fun i x => by
      simp only [LinearMap.comp_apply, repJetBoson_inclBoson, ← ιBoson_apply,
        repJet_ιBoson]) w

lemma repLorentzGroup_ιFermionTotal (Λ : SL(2,ℂ)) (w : T.FermionGenerators) :
    T.repLorentzGroup Λ (T.ιFermionTotal w) = T.ιFermionTotal (T.repLorentzFermion Λ w) :=
  LinearMap.congr_fun (fermionGenerators_hom_ext
    (F := (T.repLorentzGroup Λ) ∘ₗ T.ιFermionTotal)
    (F' := T.ιFermionTotal ∘ₗ T.repLorentzFermion Λ)
    fun i x => by
      simp only [LinearMap.comp_apply, repLorentzFermion_inclFermion, ← ιFermion_apply,
        repLorentzGroup_ιFermion]) w

lemma repLorentzGroup_ιBosonTotal (Λ : SL(2,ℂ)) (w : T.BosonGenerators) :
    T.repLorentzGroup Λ (T.ιBosonTotal w) = T.ιBosonTotal (T.repLorentzBoson Λ w) :=
  LinearMap.congr_fun (bosonGenerators_hom_ext
    (F := (T.repLorentzGroup Λ) ∘ₗ T.ιBosonTotal)
    (F' := T.ιBosonTotal ∘ₗ T.repLorentzBoson Λ)
    fun i x => by
      simp only [LinearMap.comp_apply, repLorentzBoson_inclBoson, ← ιBoson_apply,
        repLorentzGroup_ιBoson]) w

lemma massWeightScale_ιFermionTotal (c : ℝ) (w : T.FermionGenerators) :
    T.massWeightScale c (T.ιFermionTotal w)
      = T.ιFermionTotal (T.massWeightScaleFermion (c : ℂ) w) :=
  LinearMap.congr_fun (fermionGenerators_hom_ext
    (F := (T.massWeightScale c).toLinearMap ∘ₗ T.ιFermionTotal)
    (F' := T.ιFermionTotal ∘ₗ T.massWeightScaleFermion (c : ℂ))
    fun i x => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        massWeightScaleFermion_inclFermion, ← ιFermion_apply, massWeightScale_ιFermion]) w

lemma massWeightScale_ιBosonTotal (c : ℝ) (w : T.BosonGenerators) :
    T.massWeightScale c (T.ιBosonTotal w)
      = T.ιBosonTotal (T.massWeightScaleBoson (c : ℂ) w) :=
  LinearMap.congr_fun (bosonGenerators_hom_ext
    (F := (T.massWeightScale c).toLinearMap ∘ₗ T.ιBosonTotal)
    (F' := T.ιBosonTotal ∘ₗ T.massWeightScaleBoson (c : ℂ))
    fun i x => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        massWeightScaleBoson_inclBoson, ← ιBoson_apply, massWeightScale_ιBoson]) w

end Total

/-! ### Maps of generator spaces -/

/-- A map of generator spaces between two field data over one gauge datum: linear maps of
  the fermionic and of the bosonic generator spaces intertwining the jet gauge action, the
  Lorentz action and the mass-weight scaling. The connection generators are shared. -/
structure GenHom (T T' : GaugeFieldData jets) where
  fermion : T.FermionGenerators →ₗ[ℂ] T'.FermionGenerators
  boson : T.BosonGenerators →ₗ[ℂ] T'.BosonGenerators
  fermion_repJet : ∀ U v, fermion (T.repJetFermion U v) = T'.repJetFermion U (fermion v)
  boson_repJet : ∀ U v, boson (T.repJetBoson U v) = T'.repJetBoson U (boson v)
  fermion_repLorentz : ∀ Λ v,
    fermion (T.repLorentzFermion Λ v) = T'.repLorentzFermion Λ (fermion v)
  boson_repLorentz : ∀ Λ v, boson (T.repLorentzBoson Λ v) = T'.repLorentzBoson Λ (boson v)
  fermion_scale : ∀ (c : ℂ) v,
    fermion (T.massWeightScaleFermion c v) = T'.massWeightScaleFermion c (fermion v)
  boson_scale : ∀ (c : ℂ) v,
    boson (T.massWeightScaleBoson c v) = T'.massWeightScaleBoson c (boson v)

namespace GenHom

variable {T T' T'' : GaugeFieldData jets} (F : GenHom T T')

/-- The assignment of the generators of `T` in `J(T')` induced by a map of generator
  spaces. The relations hold because the images are generators of the same kind. -/
noncomputable def toAssignment : T.Assignment T'.LocalFieldAlgebra where
  fermion i := T'.ιFermionTotal ∘ₗ F.fermion ∘ₗ T.inclFermion i
  boson j := T'.ιBosonTotal ∘ₗ F.boson ∘ₗ T.inclBoson j
  connection := T'.ιConnection
  fermion_mul_self _ _ := ιFermionTotal_mul_self _
  fermion_mul_swap _ _ _ _ := ιFermionTotal_mul_swap _ _
  boson_commute _ _ _ _ := ιBosonTotal_commute _ _
  connection_commute _ _ := ιConnection_commute _ _
  boson_commute_connection _ _ _ := ιBosonTotal_commute_ιConnection _ _
  boson_commute_fermion _ _ _ _ := ιBosonTotal_commute_ιFermionTotal _ _
  connection_commute_fermion _ _ _ := ιConnection_commute_ιFermionTotal _ _

/-- The algebra map `J(T) → J(T')` induced by a map of generator spaces. -/
noncomputable def toAlgHom : T.LocalFieldAlgebra →ₐ[ℂ] T'.LocalFieldAlgebra :=
  F.toAssignment.lift

@[simp]
lemma toAlgHom_ιFermionTotal (v : T.FermionGenerators) :
    F.toAlgHom (T.ιFermionTotal v) = T'.ιFermionTotal (F.fermion v) := by
  rw [toAlgHom, Assignment.lift_ιFermionTotal]
  exact LinearMap.congr_fun (fermionGenerators_hom_ext
    (F := F.toAssignment.fermionTotal) (F' := T'.ιFermionTotal ∘ₗ F.fermion)
    fun i x => by simp [toAssignment]) v

@[simp]
lemma toAlgHom_ιBosonTotal (v : T.BosonGenerators) :
    F.toAlgHom (T.ιBosonTotal v) = T'.ιBosonTotal (F.boson v) := by
  rw [toAlgHom, Assignment.lift_ιBosonTotal]
  exact LinearMap.congr_fun (bosonGenerators_hom_ext
    (F := F.toAssignment.bosonTotal) (F' := T'.ιBosonTotal ∘ₗ F.boson)
    fun i x => by simp [toAssignment]) v

@[simp]
lemma toAlgHom_ιConnection (v : GaugeBoson.JetComponentSpace 𝔤) :
    F.toAlgHom (T.ιConnection v) = T'.ιConnection v :=
  F.toAssignment.lift_ιConnection v

/-- The induced assignment is equivariant for the two actions of `J(T')`. -/
lemma toAssignment_isEquivariant :
    F.toAssignment.IsEquivariant T'.repJet T'.repLorentzGroup where
  repJet_fermion U i x := by
    show T'.repJet U (T'.ιFermionTotal (F.fermion (T.inclFermion i x)))
      = T'.ιFermionTotal (F.fermion (T.inclFermion i (JetComponentSpace.repJet _ U x)))
    rw [repJet_ιFermionTotal, ← F.fermion_repJet, repJetFermion_inclFermion]
  repJet_boson U j y := by
    show T'.repJet U (T'.ιBosonTotal (F.boson (T.inclBoson j y)))
      = T'.ιBosonTotal (F.boson (T.inclBoson j (JetComponentSpace.repJet _ U y)))
    rw [repJet_ιBosonTotal, ← F.boson_repJet, repJetBoson_inclBoson]
  repJet_connection U v := repJet_ιConnection_affine U v
  repLorentz_fermion Λ i x := by
    show T'.repLorentzGroup Λ (T'.ιFermionTotal (F.fermion (T.inclFermion i x)))
      = T'.ιFermionTotal (F.fermion (T.inclFermion i
          (JetComponentSpace.repLorentzGroup _ Λ x)))
    rw [repLorentzGroup_ιFermionTotal, ← F.fermion_repLorentz, repLorentzFermion_inclFermion]
  repLorentz_boson Λ j y := by
    show T'.repLorentzGroup Λ (T'.ιBosonTotal (F.boson (T.inclBoson j y)))
      = T'.ιBosonTotal (F.boson (T.inclBoson j (JetComponentSpace.repLorentzGroup _ Λ y)))
    rw [repLorentzGroup_ιBosonTotal, ← F.boson_repLorentz, repLorentzBoson_inclBoson]
  repLorentz_connection Λ v := repLorentzGroup_ιConnection_eq Λ v

/-- **A map of generator spaces is a realization**: `J(T')` carries the fields of `T`. -/
noncomputable def toRealization :
    Realization T T'.LocalFieldAlgebra T'.repJet T'.repLorentzGroup :=
  F.toAssignment_isEquivariant.toRealization repJet_apply_mul repLorentzGroup_apply_mul

lemma toAlgHom_repJet (U : GJ) (x : T.LocalFieldAlgebra) :
    F.toAlgHom (T.repJet U x) = T'.repJet U (F.toAlgHom x) :=
  F.toRealization.map_repJet U x

lemma toAlgHom_repLorentzGroup (Λ : SL(2,ℂ)) (x : T.LocalFieldAlgebra) :
    F.toAlgHom (T.repLorentzGroup Λ x) = T'.repLorentzGroup Λ (F.toAlgHom x) :=
  F.toRealization.map_repLorentz Λ x

/-- The induced algebra map respects the mass-weight scaling. -/
lemma toAlgHom_massWeightScale (c : ℝ) (x : T.LocalFieldAlgebra) :
    F.toAlgHom (T.massWeightScale c x) = T'.massWeightScale c (F.toAlgHom x) := by
  have h : F.toAlgHom.comp (T.massWeightScale c) = (T'.massWeightScale c).comp F.toAlgHom := by
    refine algHom_ext (fun i x => ?_) (fun j y => ?_) (fun v => ?_)
    · simp only [AlgHom.comp_apply, ιFermion_apply, massWeightScale_ιFermionTotal,
        toAlgHom_ιFermionTotal, F.fermion_scale]
    · simp only [AlgHom.comp_apply, ιBoson_apply, massWeightScale_ιBosonTotal,
        toAlgHom_ιBosonTotal, F.boson_scale]
    · simp only [AlgHom.comp_apply, massWeightScale_ιConnection, toAlgHom_ιConnection]
  exact AlgHom.congr_fun h x

/-- The identity map of generator spaces. -/
def id (T : GaugeFieldData jets) : GenHom T T where
  fermion := LinearMap.id
  boson := LinearMap.id
  fermion_repJet _ _ := rfl
  boson_repJet _ _ := rfl
  fermion_repLorentz _ _ := rfl
  boson_repLorentz _ _ := rfl
  fermion_scale _ _ := rfl
  boson_scale _ _ := rfl

/-- The composite of two maps of generator spaces. -/
def comp (G : GenHom T' T'') : GenHom T T'' where
  fermion := G.fermion ∘ₗ F.fermion
  boson := G.boson ∘ₗ F.boson
  fermion_repJet U v := by simp [F.fermion_repJet, G.fermion_repJet]
  boson_repJet U v := by simp [F.boson_repJet, G.boson_repJet]
  fermion_repLorentz Λ v := by simp [F.fermion_repLorentz, G.fermion_repLorentz]
  boson_repLorentz Λ v := by simp [F.boson_repLorentz, G.boson_repLorentz]
  fermion_scale c v := by simp [F.fermion_scale, G.fermion_scale]
  boson_scale c v := by simp [F.boson_scale, G.boson_scale]

/-- Functoriality: the identity. -/
lemma toAlgHom_id : (GenHom.id T).toAlgHom = AlgHom.id ℂ T.LocalFieldAlgebra :=
  algHom_ext (fun i x => by simp [ιFermion_apply, GenHom.id])
    (fun j y => by simp [ιBoson_apply, GenHom.id]) (fun v => by simp)

/-- Functoriality: composition. -/
lemma toAlgHom_comp (G : GenHom T' T'') :
    (F.comp G).toAlgHom = G.toAlgHom.comp F.toAlgHom :=
  algHom_ext (fun i x => by simp [ιFermion_apply, GenHom.comp])
    (fun j y => by simp [ιBoson_apply, GenHom.comp]) (fun v => by simp)

end GenHom

/-! ### Equivalences and the transport of invariants -/

/-- An equivalence of generator spaces: linear equivalences of the fermionic and of the
  bosonic generator spaces intertwining the jet gauge action, the Lorentz action and the
  mass-weight scaling. -/
structure GenEquiv (T T' : GaugeFieldData jets) where
  fermion : T.FermionGenerators ≃ₗ[ℂ] T'.FermionGenerators
  boson : T.BosonGenerators ≃ₗ[ℂ] T'.BosonGenerators
  fermion_repJet : ∀ U v, fermion (T.repJetFermion U v) = T'.repJetFermion U (fermion v)
  boson_repJet : ∀ U v, boson (T.repJetBoson U v) = T'.repJetBoson U (boson v)
  fermion_repLorentz : ∀ Λ v,
    fermion (T.repLorentzFermion Λ v) = T'.repLorentzFermion Λ (fermion v)
  boson_repLorentz : ∀ Λ v, boson (T.repLorentzBoson Λ v) = T'.repLorentzBoson Λ (boson v)
  fermion_scale : ∀ (c : ℂ) v,
    fermion (T.massWeightScaleFermion c v) = T'.massWeightScaleFermion c (fermion v)
  boson_scale : ∀ (c : ℂ) v,
    boson (T.massWeightScaleBoson c v) = T'.massWeightScaleBoson c (boson v)

namespace GenEquiv

variable {T T' : GaugeFieldData jets} (E : GenEquiv T T')

/-- The underlying map of generator spaces. -/
def toHom : GenHom T T' where
  fermion := E.fermion.toLinearMap
  boson := E.boson.toLinearMap
  fermion_repJet := E.fermion_repJet
  boson_repJet := E.boson_repJet
  fermion_repLorentz := E.fermion_repLorentz
  boson_repLorentz := E.boson_repLorentz
  fermion_scale := E.fermion_scale
  boson_scale := E.boson_scale

/-- The inverse equivalence: an inverse of an intertwiner is an intertwiner. -/
def symm : GenEquiv T' T where
  fermion := E.fermion.symm
  boson := E.boson.symm
  fermion_repJet U v := E.fermion.injective (by simp [E.fermion_repJet])
  boson_repJet U v := E.boson.injective (by simp [E.boson_repJet])
  fermion_repLorentz Λ v := E.fermion.injective (by simp [E.fermion_repLorentz])
  boson_repLorentz Λ v := E.boson.injective (by simp [E.boson_repLorentz])
  fermion_scale c v := E.fermion.injective (by simp [E.fermion_scale])
  boson_scale c v := E.boson.injective (by simp [E.boson_scale])

/-- The algebra equivalence `J(T) ≃ J(T')` of an equivalence of generator spaces. -/
noncomputable def toAlgEquiv : T.LocalFieldAlgebra ≃ₐ[ℂ] T'.LocalFieldAlgebra :=
  AlgEquiv.ofAlgHom E.toHom.toAlgHom E.symm.toHom.toAlgHom
    (algHom_ext (fun i x => by simp [ιFermion_apply, toHom, symm])
      (fun j y => by simp [ιBoson_apply, toHom, symm]) (fun v => by simp))
    (algHom_ext (fun i x => by simp [ιFermion_apply, toHom, symm])
      (fun j y => by simp [ιBoson_apply, toHom, symm]) (fun v => by simp))

/-- **Equivalent descriptions of a theory have the same invariants**: the gauge and
  Lorentz invariants of mass weight at most `w` of `T` are carried onto those of `T'`. -/
theorem invariantsLE_map (w : ℕ) :
    (T.invariantsLE w).map (E.toAlgEquiv : T.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = T'.invariantsLE w :=
  GaugeFieldData.invariantsLE_map E.toAlgEquiv E.toHom.toAlgHom_repJet
    E.toHom.toAlgHom_repLorentzGroup E.toHom.toAlgHom_massWeightScale w

end GenEquiv

/-! ### Species-wise isomorphisms -/

/-- A species-wise isomorphism of field data: bijections of the fermionic and of the bosonic
  species, and for each species a linear equivalence of value spaces intertwining the
  Lorentz and jet gauge actions, between matter fields of the same mass weight. -/
structure SpeciesEquiv (T T' : GaugeFieldData jets) where
  fermionEquiv : T.FermionSpecies ≃ T'.FermionSpecies
  bosonEquiv : T.BosonSpecies ≃ T'.BosonSpecies
  fermion : ∀ i, (T'.fermion (fermionEquiv i)).V ≃ₗ[ℂ] (T.fermion i).V
  boson : ∀ j, (T'.boson (bosonEquiv j)).V ≃ₗ[ℂ] (T.boson j).V
  fermion_repLorentz : ∀ i Λ, (fermion i).toLinearMap ∘ₗ (T'.fermion (fermionEquiv i)).repLorentz Λ
    = (T.fermion i).repLorentz Λ ∘ₗ (fermion i).toLinearMap
  boson_repLorentz : ∀ j Λ, (boson j).toLinearMap ∘ₗ (T'.boson (bosonEquiv j)).repLorentz Λ
    = (T.boson j).repLorentz Λ ∘ₗ (boson j).toLinearMap
  fermion_repJet : ∀ i U,
    (fermion i).toLinearMap.lTensor SpaceTimeAlgebra ∘ₗ (T'.fermion (fermionEquiv i)).repJet U
      = (T.fermion i).repJet U ∘ₗ (fermion i).toLinearMap.lTensor SpaceTimeAlgebra
  boson_repJet : ∀ j U,
    (boson j).toLinearMap.lTensor SpaceTimeAlgebra ∘ₗ (T'.boson (bosonEquiv j)).repJet U
      = (T.boson j).repJet U ∘ₗ (boson j).toLinearMap.lTensor SpaceTimeAlgebra
  fermion_massWeight : ∀ i, (T'.fermion (fermionEquiv i)).massWeight = (T.fermion i).massWeight
  boson_massWeight : ∀ j, (T'.boson (bosonEquiv j)).massWeight = (T.boson j).massWeight

namespace SpeciesEquiv

variable {T T' : GaugeFieldData jets} (S : SpeciesEquiv T T')

/-- The equivalence of fermionic generator spaces: the symbols of a species of `T` are the
  pulled-back symbols of the species of `T'` it corresponds to. -/
noncomputable def fermionGen : T.FermionGenerators ≃ₗ[ℂ] T'.FermionGenerators :=
  DirectSum.lequivOfEquiv S.fermionEquiv
    (A := fun i => JetComponentSpace (T.fermion i)) (B := fun k => JetComponentSpace (T'.fermion k))
    fun i => JetComponentSpace.comapEquiv (S.fermion i)

/-- The equivalence of bosonic generator spaces. -/
noncomputable def bosonGen : T.BosonGenerators ≃ₗ[ℂ] T'.BosonGenerators :=
  DirectSum.lequivOfEquiv S.bosonEquiv
    (A := fun i => JetComponentSpace (T.boson i)) (B := fun k => JetComponentSpace (T'.boson k))
    fun j => JetComponentSpace.comapEquiv (S.boson j)

lemma fermionGen_inclFermion (i : T.FermionSpecies) (x : JetComponentSpace (T.fermion i)) :
    S.fermionGen (T.inclFermion i x)
      = T'.inclFermion (S.fermionEquiv i) (JetComponentSpace.comap (S.fermion i).toLinearMap x) :=
  DirectSum.lequivOfEquiv_lof (A := fun i => JetComponentSpace (T.fermion i))
    (B := fun k => JetComponentSpace (T'.fermion k)) S.fermionEquiv
    (fun i => JetComponentSpace.comapEquiv (S.fermion i)) i x

lemma bosonGen_inclBoson (j : T.BosonSpecies) (y : JetComponentSpace (T.boson j)) :
    S.bosonGen (T.inclBoson j y)
      = T'.inclBoson (S.bosonEquiv j) (JetComponentSpace.comap (S.boson j).toLinearMap y) :=
  DirectSum.lequivOfEquiv_lof (A := fun i => JetComponentSpace (T.boson i))
    (B := fun k => JetComponentSpace (T'.boson k)) S.bosonEquiv
    (fun j => JetComponentSpace.comapEquiv (S.boson j)) j y

/-- **A species-wise isomorphism is an equivalence of generator spaces.** -/
noncomputable def toGenEquiv : GenEquiv T T' where
  fermion := S.fermionGen
  boson := S.bosonGen
  fermion_repJet U v := LinearMap.congr_fun (fermionGenerators_hom_ext
    (F := S.fermionGen.toLinearMap ∘ₗ T.repJetFermion U)
    (F' := T'.repJetFermion U ∘ₗ S.fermionGen.toLinearMap) fun i x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, repJetFermion_inclFermion,
        fermionGen_inclFermion]
      exact congrArg _ (LinearMap.congr_fun
        (JetComponentSpace.comap_comp_repJet _ (S.fermion_repJet i) U) x)) v
  boson_repJet U v := LinearMap.congr_fun (bosonGenerators_hom_ext
    (F := S.bosonGen.toLinearMap ∘ₗ T.repJetBoson U)
    (F' := T'.repJetBoson U ∘ₗ S.bosonGen.toLinearMap) fun j y => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, repJetBoson_inclBoson,
        bosonGen_inclBoson]
      exact congrArg _ (LinearMap.congr_fun
        (JetComponentSpace.comap_comp_repJet _ (S.boson_repJet j) U) y)) v
  fermion_repLorentz Λ v := LinearMap.congr_fun (fermionGenerators_hom_ext
    (F := S.fermionGen.toLinearMap ∘ₗ T.repLorentzFermion Λ)
    (F' := T'.repLorentzFermion Λ ∘ₗ S.fermionGen.toLinearMap) fun i x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, repLorentzFermion_inclFermion,
        fermionGen_inclFermion]
      exact congrArg _ (LinearMap.congr_fun
        (JetComponentSpace.comap_comp_repLorentzGroup _ (S.fermion_repLorentz i) Λ) x)) v
  boson_repLorentz Λ v := LinearMap.congr_fun (bosonGenerators_hom_ext
    (F := S.bosonGen.toLinearMap ∘ₗ T.repLorentzBoson Λ)
    (F' := T'.repLorentzBoson Λ ∘ₗ S.bosonGen.toLinearMap) fun j y => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, repLorentzBoson_inclBoson,
        bosonGen_inclBoson]
      exact congrArg _ (LinearMap.congr_fun
        (JetComponentSpace.comap_comp_repLorentzGroup _ (S.boson_repLorentz j) Λ) y)) v
  fermion_scale c v := LinearMap.congr_fun (fermionGenerators_hom_ext
    (F := S.fermionGen.toLinearMap ∘ₗ T.massWeightScaleFermion c)
    (F' := T'.massWeightScaleFermion c ∘ₗ S.fermionGen.toLinearMap) fun i x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, massWeightScaleFermion_inclFermion,
        fermionGen_inclFermion]
      rw [S.fermion_massWeight i]
      exact congrArg _ (LinearMap.congr_fun
        (JetComponentSpace.comap_comp_massWeightScale (S.fermion i).toLinearMap _ c) x)) v
  boson_scale c v := LinearMap.congr_fun (bosonGenerators_hom_ext
    (F := S.bosonGen.toLinearMap ∘ₗ T.massWeightScaleBoson c)
    (F' := T'.massWeightScaleBoson c ∘ₗ S.bosonGen.toLinearMap) fun j y => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, massWeightScaleBoson_inclBoson,
        bosonGen_inclBoson]
      rw [S.boson_massWeight j]
      exact congrArg _ (LinearMap.congr_fun
        (JetComponentSpace.comap_comp_massWeightScale (S.boson j).toLinearMap _ c) y)) v

/-- **Two descriptions of a theory that differ by a renaming of the species and by
  isomorphisms of their matter fields have the same invariants.** -/
theorem invariantsLE_map (w : ℕ) :
    (T.invariantsLE w).map
        (S.toGenEquiv.toAlgEquiv : T.LocalFieldAlgebra →ₗ[ℂ] T'.LocalFieldAlgebra)
      = T'.invariantsLE w :=
  S.toGenEquiv.invariantsLE_map w

end SpeciesEquiv

/-! ### Species-wise morphisms, not necessarily invertible -/

end GaugeFieldData

/-- The data of an intertwiner of matter fields that the symbols see: the 6 November
  `MatterField.Hom` without its gauge-algebra and statistic fields. -/
structure MatterField.SymbolHom {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
    {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J} (M N : MatterField jets) where
  toLinearMap : M.V →ₗ[ℂ] N.V
  repLorentz_comm : ∀ Λ, toLinearMap ∘ₗ M.repLorentz Λ = N.repLorentz Λ ∘ₗ toLinearMap
  repJet_comm : ∀ U, toLinearMap.lTensor SpaceTimeAlgebra ∘ₗ M.repJet U
      = N.repJet U ∘ₗ toLinearMap.lTensor SpaceTimeAlgebra
  massWeight_eq : M.massWeight = N.massWeight

namespace GaugeFieldData

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
  {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
  {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

/-- A species-wise morphism `T → T'` of field data: every species of `T'` receives an
  intertwiner from one species of `T`. -/
structure SpeciesHom (T T' : GaugeFieldData jets) where
  fermionIdx : T'.FermionSpecies → T.FermionSpecies
  bosonIdx : T'.BosonSpecies → T.BosonSpecies
  fermion : ∀ j, MatterField.SymbolHom (T.fermion (fermionIdx j)) (T'.fermion j)
  boson : ∀ j, MatterField.SymbolHom (T.boson (bosonIdx j)) (T'.boson j)

namespace SpeciesHom

variable {T T' : GaugeFieldData jets} (F : SpeciesHom T T')

/-- The induced map of fermionic generator spaces, in the opposite direction: a symbol of
  a species of `T'` is pulled back to a symbol of the species of `T` it receives. -/
noncomputable def fermionGen : T'.FermionGenerators →ₗ[ℂ] T.FermionGenerators :=
  T'.assembleFermion fun j =>
    T.inclFermion (F.fermionIdx j) ∘ₗ JetComponentSpace.comap (F.fermion j).toLinearMap

/-- The induced map of bosonic generator spaces, in the opposite direction. -/
noncomputable def bosonGen : T'.BosonGenerators →ₗ[ℂ] T.BosonGenerators :=
  T'.assembleBoson fun j =>
    T.inclBoson (F.bosonIdx j) ∘ₗ JetComponentSpace.comap (F.boson j).toLinearMap

@[simp]
lemma fermionGen_inclFermion (j : T'.FermionSpecies) (x : JetComponentSpace (T'.fermion j)) :
    F.fermionGen (T'.inclFermion j x)
      = T.inclFermion (F.fermionIdx j) (JetComponentSpace.comap (F.fermion j).toLinearMap x) :=
  assembleFermion_inclFermion _ j x

@[simp]
lemma bosonGen_inclBoson (j : T'.BosonSpecies) (y : JetComponentSpace (T'.boson j)) :
    F.bosonGen (T'.inclBoson j y)
      = T.inclBoson (F.bosonIdx j) (JetComponentSpace.comap (F.boson j).toLinearMap y) :=
  assembleBoson_inclBoson _ j y

/-- **A species-wise morphism `T → T'` is a map of generator spaces from `T'` to `T`**: the
  pulled-back symbols transform as the symbols they are pulled back to. -/
noncomputable def toGenHom : GenHom T' T where
  fermion := F.fermionGen
  boson := F.bosonGen
  fermion_repJet U v := LinearMap.congr_fun (fermionGenerators_hom_ext
    (F := F.fermionGen ∘ₗ T'.repJetFermion U) (F' := T.repJetFermion U ∘ₗ F.fermionGen)
    fun j x => by
      simp only [LinearMap.comp_apply, repJetFermion_inclFermion, fermionGen_inclFermion]
      exact congrArg _ (LinearMap.congr_fun
        (JetComponentSpace.comap_comp_repJet _ (F.fermion j).repJet_comm U) x)) v
  boson_repJet U v := LinearMap.congr_fun (bosonGenerators_hom_ext
    (F := F.bosonGen ∘ₗ T'.repJetBoson U) (F' := T.repJetBoson U ∘ₗ F.bosonGen)
    fun j y => by
      simp only [LinearMap.comp_apply, repJetBoson_inclBoson, bosonGen_inclBoson]
      exact congrArg _ (LinearMap.congr_fun
        (JetComponentSpace.comap_comp_repJet _ (F.boson j).repJet_comm U) y)) v
  fermion_repLorentz Λ v := LinearMap.congr_fun (fermionGenerators_hom_ext
    (F := F.fermionGen ∘ₗ T'.repLorentzFermion Λ) (F' := T.repLorentzFermion Λ ∘ₗ F.fermionGen)
    fun j x => by
      simp only [LinearMap.comp_apply, repLorentzFermion_inclFermion, fermionGen_inclFermion]
      exact congrArg _ (LinearMap.congr_fun
        (JetComponentSpace.comap_comp_repLorentzGroup _ (F.fermion j).repLorentz_comm Λ) x)) v
  boson_repLorentz Λ v := LinearMap.congr_fun (bosonGenerators_hom_ext
    (F := F.bosonGen ∘ₗ T'.repLorentzBoson Λ) (F' := T.repLorentzBoson Λ ∘ₗ F.bosonGen)
    fun j y => by
      simp only [LinearMap.comp_apply, repLorentzBoson_inclBoson, bosonGen_inclBoson]
      exact congrArg _ (LinearMap.congr_fun
        (JetComponentSpace.comap_comp_repLorentzGroup _ (F.boson j).repLorentz_comm Λ) y)) v
  fermion_scale c v := LinearMap.congr_fun (fermionGenerators_hom_ext
    (F := F.fermionGen ∘ₗ T'.massWeightScaleFermion c)
    (F' := T.massWeightScaleFermion c ∘ₗ F.fermionGen)
    fun j x => by
      simp only [LinearMap.comp_apply, massWeightScaleFermion_inclFermion,
        fermionGen_inclFermion]
      rw [(F.fermion j).massWeight_eq]
      exact congrArg _ (LinearMap.congr_fun
        (JetComponentSpace.comap_comp_massWeightScale (F.fermion j).toLinearMap _ c) x)) v
  boson_scale c v := LinearMap.congr_fun (bosonGenerators_hom_ext
    (F := F.bosonGen ∘ₗ T'.massWeightScaleBoson c)
    (F' := T.massWeightScaleBoson c ∘ₗ F.bosonGen)
    fun j y => by
      simp only [LinearMap.comp_apply, massWeightScaleBoson_inclBoson, bosonGen_inclBoson]
      rw [(F.boson j).massWeight_eq]
      exact congrArg _ (LinearMap.congr_fun
        (JetComponentSpace.comap_comp_massWeightScale (F.boson j).toLinearMap _ c) y)) v

/-- **A species-wise morphism `T → T'` realizes `T'` in the algebra of `T`.** -/
noncomputable def toRealization :
    Realization T' T.LocalFieldAlgebra T.repJet T.repLorentzGroup :=
  F.toGenHom.toRealization

end SpeciesHom

end GaugeFieldData

#print axioms GaugeFieldData.GenHom.toRealization
#print axioms GaugeFieldData.GenHom.toAlgHom_comp
#print axioms GaugeFieldData.GenEquiv.invariantsLE_map
#print axioms GaugeFieldData.SpeciesEquiv.invariantsLE_map
#print axioms GaugeFieldData.SpeciesHom.toRealization
