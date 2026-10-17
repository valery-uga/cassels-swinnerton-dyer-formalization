import PfaffianDescent.SheafFreeIso
import Mathlib.AlgebraicGeometry.Modules.Sheaf

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v w t
section
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A covering by actual free sheaf identifications proves local freeness. -/
lemma sheaf_isLocallyFree_of_coverIso (M : SheafOfModules.{u} R)
    {ι : Type t} (U : ι → C) (hU : J.CoversTop U) (I : ι → Type u)
    (e : ∀ i, SheafOfModules.free (R := R.over (U i)) (I i) ≅ M.over (U i)) :
    M.IsLocallyFree := by
  let G : M.LocalGeneratorsData :=
    { I := ι
      X := U
      coversTop := hU
      generators i :=
        { I := I i
          s := (M.over (U i)).freeHomEquiv (e i).hom
          epi := by rw [Equiv.symm_apply_apply]; infer_instance } }
  haveI : G.IsLocallyFreeData := by
    refine { isIso := fun i => ?_ }
    change IsIso ((M.over (U i)).freeHomEquiv.symm ((M.over (U i)).freeHomEquiv (e i).hom))
    rw [Equiv.symm_apply_apply]
    infer_instance
  exact G.isLocallyFree

end

/-- A module sheaf is locally free when every point admits an open
neighborhood on which it has an explicit free presentation. -/
lemma sheaf_isLocallyFree_of_pointwise_free
    (X : Scheme.{u}) (M : SheafOfModules.{u} X.ringCatSheaf)
    (U : X → X.Opens) (hU : ∀ x, x ∈ U x)
    (I : X → Type u)
    (e : ∀ x, SheafOfModules.free (R := X.ringCatSheaf.over (U x)) (I x) ≅
      M.over (U x)) :
    M.IsLocallyFree := by
  apply sheaf_isLocallyFree_of_coverIso X.ringCatSheaf M U ?_ I e
  exact (Opens.coversTop_iff _ _).mpr (by
    apply TopologicalSpace.IsOpenCover.mk
    apply le_antisymm le_top
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨x, hU x⟩)

/-- If the points at which a sheaf could fail to be free form an empty set,
the pointwise free presentations give a locally free sheaf. -/
lemma sheaf_isLocallyFree_of_badLocus_eq_empty
    (X : Scheme.{u}) (M : SheafOfModules.{u} X.ringCatSheaf)
    (B : Set X) (hB : B = ∅)
    (U : ∀ x : X, x ∉ B → X.Opens)
    (hU : ∀ (x : X) (hx : x ∉ B), x ∈ U x hx)
    (I : ∀ (x : X) (hx : x ∉ B), Type u)
    (e : ∀ (x : X) (hx : x ∉ B),
      SheafOfModules.free (R := X.ringCatSheaf.over (U x hx)) (I x hx) ≅
        M.over (U x hx)) :
    M.IsLocallyFree := by
  exact sheaf_isLocallyFree_of_pointwise_free X M
    (fun x => U x (by simp [hB]))
    (fun x => hU x (by simp [hB]))
    (fun x => I x (by simp [hB]))
    (fun x => e x (by simp [hB]))

/-- An abstract locally free sheaf supplies an explicit free presentation on
some open neighborhood of every point.  This is the pointwise form of the
covering data in `IsLocallyFree`; it is useful when a later local argument
needs a concrete trivialization rather than only the class-valued predicate. -/
theorem IsLocallyFree.exists_pointwise_freeNeighborhood
    (X : Scheme.{u}) (M : SheafOfModules.{u} X.ringCatSheaf)
    [M.IsLocallyFree] (x : X) :
    ∃ (U : X.Opens) (I : Type u), x ∈ U ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData (M := M)
  letI : q.IsLocallyFreeData := hq
  let q' := q.shrink
  letI : q'.IsLocallyFreeData := inferInstance
  have hcover : (⨆ i, q'.X i) = (⊤ : X.Opens) :=
    (Opens.coversTop_iff _ _).mp q'.coversTop
  have hx : x ∈ (⨆ i, q'.X i) := by
    rw [hcover]
    trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hx
  obtain ⟨i, hxi⟩ := hx
  refine ⟨q'.X i, q'.generators i |>.I, hxi, ?_⟩
  exact ⟨asIso (q'.generators i).π⟩

/-- The free neighborhood can be chosen affine.  We refine the neighborhood
from the locally-free cover by an affine open and restrict the free
presentation along the resulting open immersion. -/
theorem IsLocallyFree.exists_pointwise_affine_freeNeighborhood
    (X : Scheme.{u}) (M : SheafOfModules.{u} X.ringCatSheaf)
    [M.IsLocallyFree] (x : X) :
    ∃ (U : X.Opens) (I : Type u), x ∈ U ∧
      IsAffineOpen U ∧
      Nonempty (SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) := by
  obtain ⟨U, I, hxU, ⟨t⟩⟩ := IsLocallyFree.exists_pointwise_freeNeighborhood X M x
  obtain ⟨V, hVaff, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
  refine ⟨V, I, hxV, hVaff, ?_⟩
  let f : V ⟶ U := homOfLE hVU
  let F := SheafOfModules.overMap X.ringCatSheaf f
  letI hpres : PreservesColimitsOfShape (Discrete I) F := inferInstance
  let η : SheafOfModules.unit (X.ringCatSheaf.over V) ≅
      F.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (SheafOfModules.overMapUnitIso f).symm
  let tV : SheafOfModules.free (R := X.ringCatSheaf.over V) I ≅ M.over V :=
    (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I hpres η) ≪≫
      F.mapIso t ≪≫ (SheafOfModules.overFunctorMap X.ringCatSheaf f).app M
  exact ⟨tV⟩

end PfaffianDescent
