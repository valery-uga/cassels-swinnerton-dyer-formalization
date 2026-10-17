import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Topology.NoetherianSpace

/-! Native isomorphism on the open part belonging only to one component.
This uses reduced target closed immersions and the actual coproduct maps. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
set_option autoImplicit false

/-- Construct the native exclusive open of an actual irreducible component.
The selected closed immersion is an isomorphism there. No open, surjectivity
or isomorphism witness is an input. -/
theorem nativeReducedClosedComponent_exists_exclusiveOpen_isIso001
    {Z T : Scheme.{u}} [IsReduced T] (i : Z ⟶ T) [IsClosedImmersion i]
    (hComponent : Set.range i ∈ irreducibleComponents T)
    (hFinite : (irreducibleComponents T).Finite) :
    ∃ U : T.Opens,
      (U : Set T) = (⋃₀ (irreducibleComponents T \ {Set.range i}))ᶜ ∧
      closure (U : Set T) = Set.range i ∧
      (U : Set T).Nonempty ∧ IsIso (i ∣_ U) := by
  have hClosed : IsClosed (⋃₀ (irreducibleComponents T \ {Set.range i})) := by
    rw [Set.sUnion_eq_biUnion]
    exact hFinite.sdiff.isClosed_biUnion fun C hC =>
      isClosed_of_mem_irreducibleComponents C hC.1
  let U : T.Opens := ⟨(⋃₀ (irreducibleComponents T \ {Set.range i}))ᶜ,
    hClosed.isOpen_compl⟩
  have hClosure : closure (U : Set T) = Set.range i :=
    closure_sUnion_irreducibleComponents_sdiff_singleton hFinite _ hComponent
  have hNonempty : (U : Set T).Nonempty := by
    by_contra h
    have hEmpty : (U : Set T) = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hRange : Set.range i = ∅ := by rw [← hClosure, hEmpty, closure_empty]
    obtain ⟨z, hz⟩ := hComponent.1.1
    rw [hRange] at hz
    exact Set.notMem_empty z hz
  letI : IsClosedImmersion (i ∣_ U) :=
    IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion.{u}) inferInstance U
  have hSurj : Function.Surjective (i ∣_ U) := by
    intro x
    have hx : x.1 ∈ Set.range i := by
      rw [← hClosure]
      exact subset_closure x.2
    obtain ⟨z, hz⟩ := hx
    let zU : (i ⁻¹ᵁ U).toScheme.carrier := ⟨z, by
      change i z ∈ U
      rw [hz]
      exact x.2⟩
    refine ⟨zU, Subtype.ext ?_⟩
    exact (morphismRestrict_base_coe i U zU).trans hz
  letI : Surjective (i ∣_ U) := ⟨hSurj⟩
  letI : IsIso (i ∣_ U) := isIso_of_isClosedImmersion_of_surjective (i ∣_ U)
  exact ⟨U, rfl, hClosure, hNonempty, inferInstance⟩

/-- An actual component-indexed native coproduct map is an isomorphism on
EACH exclusive component open. The proof compares the whole map with its
selected summand, proves the selected open immersion onto the whole inverse
image, then cancels it. It never invokes transitivity on points. -/
theorem nativeReducedComponentCoproduct_exists_exclusiveOpen_wholeMap_isIso001
    {ι : Type u} (X : ι → Scheme.{u}) {W T : Scheme.{u}} [IsReduced T]
    (e : (∐ X) ≅ W) (F : W ⟶ T)
    (hClosed : ∀ i, IsClosedImmersion ((Sigma.ι X i ≫ e.hom) ≫ F))
    (c : ι ≃ irreducibleComponents T)
    (hc : ∀ i, (c i).1 = Set.range ((Sigma.ι X i ≫ e.hom) ≫ F))
    (hFinite : (irreducibleComponents T).Finite) (i : ι) :
    ∃ U : T.Opens,
      (U : Set T) =
        (⋃₀ (irreducibleComponents T \ {Set.range ((Sigma.ι X i ≫ e.hom) ≫ F)}))ᶜ ∧
      closure (U : Set T) = Set.range ((Sigma.ι X i ≫ e.hom) ≫ F) ∧
      (U : Set T).Nonempty ∧ IsIso (F ∣_ U) := by
  classical
  let a : ∀ j, X j ⟶ W := fun j => Sigma.ι X j ≫ e.hom
  let j : ∀ k, X k ⟶ T := fun k => a k ≫ F
  letI : IsClosedImmersion (j i) := hClosed i
  have hComponent : Set.range (j i) ∈ irreducibleComponents T := by
    rw [← hc i]
    exact (c i).2
  obtain ⟨U, hU, hClosure, hNonempty, hSelectedIso⟩ :=
    nativeReducedClosedComponent_exists_exclusiveOpen_isIso001 (j i) hComponent hFinite
  let V := F ⁻¹ᵁ U
  let E : (Σ k, (X k).carrier) ≃ W.carrier :=
    (AlgebraicGeometry.sigmaMk X).toEquiv.trans e.hom.homeomorph.toEquiv
  have hE (s : Σ k, (X k).carrier) : E s = a s.1 s.2 := by
    rcases s with ⟨k, z⟩
    change e.hom (AlgebraicGeometry.sigmaMk X ⟨k, z⟩) = (Sigma.ι X k ≫ e.hom) z
    rw [AlgebraicGeometry.sigmaMk_mk]
    rfl
  letI : IsOpenImmersion (a i) := by dsimp only [a]; infer_instance
  letI : IsOpenImmersion (a i ∣_ V) :=
    IsZariskiLocalAtTarget.restrict (P := @IsOpenImmersion.{u}) inferInstance V
  have hSurj : Function.Surjective (a i ∣_ V) := by
    intro y
    obtain ⟨⟨k, z⟩, hz⟩ := E.surjective y.1
    have ha : a k z = y.1 := (hE ⟨k, z⟩).symm.trans hz
    have hki : k = i := by
      by_contra hne
      have hRanges : Set.range (j k) ≠ Set.range (j i) := by
        intro h
        apply hne
        apply c.injective
        exact Subtype.ext ((hc k).trans (h.trans (hc i).symm))
      have hCne : (c k).1 ≠ Set.range (j i) := by
        intro h
        exact hRanges ((hc k).symm.trans h)
      have hOther : F y.1 ∈ ⋃₀ (irreducibleComponents T \ {Set.range (j i)}) := by
        refine Set.mem_sUnion.mpr ⟨(c k).1, ⟨(c k).2, ?_⟩, ?_⟩
        · simpa only [Set.mem_singleton_iff] using hCne
        · rw [hc k]
          exact ⟨z, congrArg F ha⟩
      have hyU : F y.1 ∈ U := y.2
      have hNot : F y.1 ∉ ⋃₀ (irreducibleComponents T \ {Set.range (j i)}) := by
        change F y.1 ∈ (⋃₀ (irreducibleComponents T \ {Set.range (j i)}))ᶜ
        rw [← hU]
        exact hyU
      exact hNot hOther
    subst k
    let zV : (a i ⁻¹ᵁ V).toScheme.carrier := ⟨z, by
      change a i z ∈ V
      rw [ha]
      exact y.2⟩
    refine ⟨zV, Subtype.ext ?_⟩
    exact (morphismRestrict_base_coe (a i) V zV).trans ha
  letI : IsIso (a i ∣_ V) := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    apply Opens.ext
    exact Set.range_eq_univ.mpr hSurj
  letI : IsIso ((a i ∣_ F ⁻¹ᵁ U) ≫ (F ∣_ U)) := by
    rw [← morphismRestrict_comp]
    exact hSelectedIso
  have hWholeIso : IsIso (F ∣_ U) :=
    IsIso.of_isIso_comp_left (a i ∣_ F ⁻¹ᵁ U) (F ∣_ U)
  exact ⟨U, hU, hClosure, hNonempty, hWholeIso⟩

end PfaffianDescent.Coray
