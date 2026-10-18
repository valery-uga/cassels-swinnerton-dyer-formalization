import PfaffianDescent.AffineHilbertBurchGlobalPhysicalLift

/-!
Physical family lifting from a Hilbert--Burch presentation over an actual
affine coefficient reduction. This consumer accepts the constructed
principal neighborhood directly, without requiring its ring to be a
particular tensor-product implementation. The principal surface
construction supplies its presentation hypotheses in the cubic application.
-/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix Module
open scoped BigOperators
universe u
set_option autoImplicit false

theorem exists_genericAffineHilbertBurch_globalPhysicalLift001
    {B S A' A : Type u} [CommRing B] [CommRing S] [IsLocalRing S]
    [CommRing A'] [CommRing A] [Algebra B S] [Algebra B A'] [Algebra B A]
    [Algebra S A] [IsScalarTower B S A]
    {X X0 : Scheme.{u}} (F : X ⟶ Spec (.of B)) [Smooth F] [IsSeparated F]
    (F0 : X0 ⟶ Spec (.of S)) (d : X0 ⟶ X)
    (Hbase : IsPullback d F0 F (Spec.map (CommRingCat.ofHom (algebraMap B S))))
    (a : Spec (.of A') ⟶ X) [IsOpenImmersion a]
    (ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap B A')))
    (π : A' →ₐ[B] A) (hπ : Function.Surjective π)
    (hker : RingHom.ker π.toRingHom =
      (RingHom.ker (algebraMap B S)).map (algebraMap B A'))
    (a0 : Spec (.of A) ⟶ X0)
    (Hchart : IsPullback (Spec.map (CommRingCat.ofHom π.toRingHom)) a0 a d)
    (hBS : Function.Surjective (algebraMap B S))
    (hI : (RingHom.ker (algebraMap B S)) ^ 2 = ⊥)
    {m : ℕ} (M : Matrix (Option (Fin m)) (Fin m) A) (J : Ideal A)
    (hJ : J = Ideal.span (Set.range (hilbertBurchCofactors318 M)))
    (hrelations : ∀ v : Option (Fin m) → A,
      (∑ i, v i * hilbertBurchCofactors318 M i) = 0 →
      ∃ w : Fin m → A, ∀ i, v i = ∑ j, M i j * w j)
    [Module.Finite S (A ⧸ J)] [Module.Flat S (A ⧸ J)]
    (n : ℕ) (hn : Module.finrank S (A ⧸ J) = n) :
    ∃ Q : FiniteFlatHilbertPoint195 F n,
      (finiteFlatHilbertBaseChange195 d F0 F
        (Spec.map (CommRingCat.ofHom (algebraMap B S))) Hbase n Q).val =
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a0).ker := by
  letI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap B A'))) := by
    rw [← ha]
    infer_instance
  letI : Module.Flat B A' := RingHom.flat_algebraMap_iff.mp
    (Flat.SpecMap_iff.mp (inferInstance : Flat
      (Spec.map (CommRingCat.ofHom (algebraMap B A')))))
  obtain ⟨N, J', _, _, hmap, _, hfinite, hfree, hflat, hrank⟩ :=
    exists_hilbertBurch_prescribedFiniteFlat_lift318 hBS hI π hπ hker M J hJ hrelations
  let Q' := A' ⧸ J'
  let i' : Spec (.of Q') ⟶ X := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫ a
  letI : Module.Finite B Q' := hfinite
  letI : Module.Free B Q' := hfree
  letI : Module.Flat B Q' := hflat
  have hbase : i' ≫ F = Spec.map (CommRingCat.ofHom (algebraMap B Q')) := by
    change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫ a) ≫ F = _
    rw [Category.assoc, ha, ← Spec.map_comp]
    rfl
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap B Q'))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfinite)
  letI : Flat (Spec.map (CommRingCat.ofHom (algebraMap B Q'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hflat)
  letI : IsFinite (i' ≫ F) := by rw [hbase]; infer_instance
  letI : Flat (i' ≫ F) := by rw [hbase]; infer_instance
  letI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  letI : IsClosedImmersion i' :=
    nativeFiniteClosedThroughOpen_isClosed314
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) a F
  have hdegree : ∀ y : Spec (.of B), (i' ≫ F).finrank y = n := by
    intro y
    rw [hbase]
    exact ((Scheme.Hom.finrank_SpecMap_algebraMap B Q' y).trans
      (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := B) (M := Q')) y)).trans
      (hrank.trans hn)
  let Q := closedImmersionHilbertPoint195 F i' n hdegree
  let ρ := prescribedQuotientReduction174 π J' J hmap
  have Hquot := prescribedQuotientReduction174_isPullback π J' J hmap
  have Hwhole : IsPullback (Spec.map (CommRingCat.ofHom ρ.toRingHom))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a0) i' d :=
    Hquot.paste_vert Hchart
  exact ⟨Q, wholeIdeal_comap_eq_of_isPullback195
    (Spec.map (CommRingCat.ofHom ρ.toRingHom))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a0) i' d Hwhole⟩

end PfaffianDescent
end
