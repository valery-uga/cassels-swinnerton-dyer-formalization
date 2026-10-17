import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpen

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_goodOpen_fieldPoint_rank
    {K : Type u} [Field K] {X Y P : Scheme.{u}}
    (g : X ⟶ Y) [IsProper g]
    [Flat (g ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen g)]
    (ep : Spec (.of K) ⟶ Y) (j : P ⟶ X) (c : P ⟶ Spec (.of K))
    (h : IsPullback j c g ep)
    (hm : ep (IsLocalRing.closedPoint K) ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen g) :
    (g ∣_ cubicClosedPointSerreFiniteZeroResidual_goodOpen g).finrank
      ⟨ep (IsLocalRing.closedPoint K), hm⟩ = c.finrank (IsLocalRing.closedPoint K) := by
  let V := cubicClosedPointSerreFiniteZeroResidual_goodOpen g
  have hr : Set.range ep ⊆ Set.range V.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : ep z ∈ V := (congrArg ep (Subsingleton.elim z (IsLocalRing.closedPoint K))) ▸ hm
    exact ⟨⟨ep z, hz⟩, rfl⟩
  let q := IsOpenImmersion.lift V.ι ep hr
  have hq : q ≫ V.ι = ep := IsOpenImmersion.lift_fac _ _ _
  have hj : Set.range j ⊆ Set.range (g ⁻¹ᵁ V).ι := by
    rintro _ ⟨z, rfl⟩
    have hz : g (j z) ∈ V := by
      have he := congrArg (fun a : P ⟶ Y => a z) h.w
      change g (j z) = ep (c z) at he
      rw [he]
      exact (congrArg ep (Subsingleton.elim (c z) (IsLocalRing.closedPoint K))) ▸ hm
    exact ⟨⟨j z, hz⟩, rfl⟩
  let u := IsOpenImmersion.lift (g ⁻¹ᵁ V).ι j hj
  have hu : u ≫ (g ⁻¹ᵁ V).ι = j := IsOpenImmersion.lift_fac _ _ _
  have hw : c ≫ q = u ≫ (g ∣_ V) := by
    apply (cancel_mono V.ι).mp
    rw [Category.assoc, hq, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, hu]
    exact h.w.symm
  have hs : IsPullback c (u ≫ (g ⁻¹ᵁ V).ι) (q ≫ V.ι) g := by
    rw [hu, hq]
    exact h.flip
  have hc : IsPullback u c (g ∣_ V) q :=
    (IsPullback.of_bot hs hw (isPullback_morphismRestrict g V)).flip
  letI : IsFinite (g ∣_ V) := cubicClosedPointSerreFiniteZeroResidual_goodOpen_finite g
  have hn := Scheme.Hom.finrank_of_isPullback u c (g ∣_ V) q hc
    (IsLocalRing.closedPoint K)
  have he : q (IsLocalRing.closedPoint K) =
      (⟨ep (IsLocalRing.closedPoint K), hm⟩ : V) := by
    apply Subtype.ext
    exact congrArg (fun a : Spec (.of K) ⟶ Y => a (IsLocalRing.closedPoint K)) hq
  rw [he] at hn
  exact hn.symm

end PfaffianDescent
