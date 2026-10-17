import PfaffianDescent.ActualPrincipalFamilyFiberChart184
import PfaffianDescent.PrincipalAffineCoordinates181

/-! Source-only189. Select a genuine upstairs affine chart at the image
of the ORIGINAL old point; its actual tensor fiber chart contains that
same point. No chart-point or target square certificate is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual open-chart base change preserves point membership, by the
native pullback range theorem and the actual H.isoPullback inverse. -/
lemma mem_range_actualBaseChangedChart189
    {X X0 V V0 : Scheme.{u}} (delta : V0 ⟶ V) (a0 : V0 ⟶ X0)
    (a : V ⟶ X) [IsOpenImmersion a] (d : X0 ⟶ X)
    (H : IsPullback delta a0 a d) (x : X0) (hx : d x ∈ Set.range a) :
    x ∈ Set.range a0 := by
  obtain ⟨y, hy⟩ := (IsOpenImmersion.range_pullbackSnd a d).ge hx
  refine ⟨H.isoPullback.inv y, ?_⟩
  calc
    a0 (H.isoPullback.inv y) = (H.isoPullback.inv ≫ a0) y :=
      (Scheme.Hom.comp_apply _ _ _).symm
    _ = (pullback.snd a d) y :=
      congrArg (fun k => k y) H.isoPullback_inv_snd
    _ = x := hy

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ORIGINAL family and ORIGINAL old point construct an upstairs
actual affine chart, its exact R scalar action, and an actual old canonical
tensor chart containing the same point with BOTH original projections. -/
lemma exists_originalPoint_actualUpstairsTensorChart189
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {X X0 : Scheme.{u}} (F : X ⟶ Spec (.of R)) (d : X0 ⟶ X)
    (F0 : X0 ⟶ Spec (.of S))
    (H : IsPullback d F0 F (Spec.map (CommRingCat.ofHom (algebraMap R S)))) (x : X0) :
    ∃ (U : X.affineOpens), d x ∈ U.1 ∧
      let A := Γ(X, U)
      letI : Algebra R A := (familySpecChartRingMap171 F U).toAlgebra
      ∃ (a0 : Spec (.of (S ⊗[R] A)) ⟶ X0) (ha0 : IsOpenImmersion a0),
        U.2.fromSpec ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
        a0 ≫ d = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫ U.2.fromSpec ∧
        a0 ≫ F0 = Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) ∧
        IsPullback (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom))
          a0 U.2.fromSpec d ∧
        x ∈ Set.range a0 ∧
        letI := ha0
        x ∈ (actualAffineChartOpen181 a0).1 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hsub⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (d x)) isOpen_univ
  let Ua : X.affineOpens := ⟨U, hU⟩
  let A := Γ(X, Ua)
  letI : Algebra R A := (familySpecChartRingMap171 F Ua).toAlgebra
  letI : IsOpenImmersion Ua.2.fromSpec := Ua.2.isOpenImmersion_fromSpec
  have ha : Ua.2.fromSpec ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
    (familySpecChartRingMap171_spec F Ua).symm
  obtain ⟨a0, ha0, hd, hs, Hchart⟩ :=
    exists_actualAffineTensorChart184 F d F0 H Ua.2.fromSpec ha
  letI := ha0
  have hxRange : d x ∈ Set.range Ua.2.fromSpec := by
    rw [Ua.2.range_fromSpec]
    exact hxU
  have hxOld : x ∈ Set.range a0 :=
    mem_range_actualBaseChangedChart189 _ a0 Ua.2.fromSpec d Hchart x hxRange
  have hxOpen : x ∈ (actualAffineChartOpen181 a0).1 := by
    change x ∈ a0 '' (Set.univ : Set (Spec (.of (S ⊗[R] A))))
    simpa only [Set.image_univ] using hxOld
  exact ⟨Ua, hxU, a0, ha0, ha, hd, hs, Hchart, hxOld, hxOpen⟩

end PfaffianDescent
