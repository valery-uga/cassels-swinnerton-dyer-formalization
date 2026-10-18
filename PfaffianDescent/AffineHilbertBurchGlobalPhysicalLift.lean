import PfaffianDescent.HilbertBurchFiniteFlatLift318
import PfaffianDescent.AffineEmbeddedSquareZeroLift174
import PfaffianDescent.NativeFiniteSubschemePushOpen314

/-!
A downstairs Hilbert--Burch presentation constructs a global finite-flat
Hilbert point with the prescribed whole-ideal special fiber. The
presentation is an explicit hypothesis of this lifting consumer; the
original Artin-support and principal-neighborhood constructions produce it
from the finite-flat surface family in the subsequent geometric application.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix Module
open scoped TensorProduct BigOperators
universe u
set_option autoImplicit false

private theorem affineHilbertLift_finiteFreeSpec_rank001
    {R Q : Type u} [CommRing R] [CommRing Q] [Algebra R Q]
    [Module.Finite R Q] [Module.Flat R Q] [Module.Free R Q] (x : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R Q))).finrank x = Module.finrank R Q :=
  (Scheme.Hom.finrank_SpecMap_algebraMap R Q x).trans
    (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := Q)) x)

/-- A genuine finite-flat downstairs HB quotient constructs an upstairs
GLOBAL physical finite-flat family, not just an affine algebra.  Ambient
charts and their base-change squares are ordinary geometric input data;
all new matrix/ideal/flatness/rank/closedness/reduction conclusions are
derived.  The original point's whole ideal can be substituted afterwards. -/
theorem exists_affineHilbertBurch_globalPhysicalLift001
    {R S A' : Type u} [CommRing R] [CommRing S] [IsLocalRing S]
    [CommRing A'] [Algebra R S] [Algebra R A']
    {X X0 : Scheme.{u}} (F : X ⟶ Spec (.of R)) [Smooth F] [IsSeparated F]
    (F0 : X0 ⟶ Spec (.of S)) (d : X0 ⟶ X)
    (Hbase : IsPullback d F0 F (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (a : Spec (.of A') ⟶ X) [IsOpenImmersion a]
    (ha : a ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A')))
    (a0 : Spec (.of (S ⊗[R] A')) ⟶ X0)
    (Hchart : IsPullback
      (Spec.map (CommRingCat.ofHom
        (affineTensorFiberReduction174 (R := R) (S := S) (A := A')).toRingHom)) a0 a d)
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    {m : ℕ} (M : Matrix (Option (Fin m)) (Fin m) (S ⊗[R] A'))
    (J : Ideal (S ⊗[R] A'))
    (hJ : J = Ideal.span (Set.range (hilbertBurchCofactors318 M)))
    (hrelations : ∀ v : Option (Fin m) → S ⊗[R] A',
      (∑ i, v i * hilbertBurchCofactors318 M i) = 0 →
      ∃ w : Fin m → S ⊗[R] A', ∀ i, v i = ∑ j, M i j * w j)
    [Module.Finite S ((S ⊗[R] A') ⧸ J)] [Module.Flat S ((S ⊗[R] A') ⧸ J)]
    (n : ℕ) (hn : Module.finrank S ((S ⊗[R] A') ⧸ J) = n) :
    ∃ (N : Matrix (Option (Fin m)) (Fin m) A') (J' : Ideal A')
      (Q : FiniteFlatHilbertPoint195 F n),
      N.map (affineTensorFiberReduction174 (R := R) (S := S) (A := A')).toRingHom = M ∧
      J' = Ideal.span (Set.range (hilbertBurchCofactors318 N)) ∧
      J'.map (affineTensorFiberReduction174 (R := R) (S := S) (A := A')).toRingHom = J ∧
      Q.val = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫ a).ker ∧
      (finiteFlatHilbertBaseChange195 d F0 F
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) Hbase n Q).val =
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a0).ker := by
  let A := S ⊗[R] A'
  let pi : A' →ₐ[R] A := affineTensorFiberReduction174
  letI : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R A'))) := by
    rw [← ha]
    infer_instance
  letI : Module.Flat R A' := RingHom.flat_algebraMap_iff.mp
    (Flat.SpecMap_iff.mp (inferInstance : Flat
      (Spec.map (CommRingCat.ofHom (algebraMap R A')))))
  have hpi : Function.Surjective pi := affineTensorFiberReduction174_surjective hRS
  have hker := affineTensorFiberReduction174_kernel (A := A') hRS
  obtain ⟨N, J', hN, hJ', hmap, hcof, hfinite, hfree, hflat, hrank⟩ :=
    exists_hilbertBurch_prescribedFiniteFlat_lift318 hRS hI pi hpi hker M J hJ hrelations
  let Q' := A' ⧸ J'
  let i' : Spec (.of Q') ⟶ X := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫ a
  letI : Module.Finite R Q' := hfinite
  letI : Module.Free R Q' := hfree
  letI : Module.Flat R Q' := hflat
  have hbase : i' ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R Q')) := by
    exact (Category.assoc (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) a F).trans
      ((congrArg (fun f => Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫ f) ha).trans
        (by rw [← Spec.map_comp]; rfl))
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R Q'))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfinite)
  letI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R Q'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hflat)
  letI : IsFinite (i' ≫ F) := by rw [hbase]; infer_instance
  letI : Flat (i' ≫ F) := by rw [hbase]; infer_instance
  letI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  letI : IsClosedImmersion i' :=
    nativeFiniteClosedThroughOpen_isClosed314
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J'))) a F
  have hdegree : ∀ y : Spec (.of R), (i' ≫ F).finrank y = n := by
    intro y
    rw [hbase]
    exact (affineHilbertLift_finiteFreeSpec_rank001 y).trans (hrank.trans hn)
  let Q := closedImmersionHilbertPoint195 F i' n hdegree
  let rho := prescribedQuotientReduction174 pi J' J hmap
  have Hquot := prescribedQuotientReduction174_isPullback pi J' J hmap
  have Hwhole : IsPullback
      (Spec.map (CommRingCat.ofHom rho.toRingHom))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a0) i' d :=
    Hquot.paste_vert Hchart
  refine ⟨N, J', Q, hN, hJ', hmap, rfl, ?_⟩
  exact wholeIdeal_comap_eq_of_isPullback195
    (Spec.map (CommRingCat.ofHom rho.toRingHom))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ a0) i' d Hwhole

end PfaffianDescent
end
