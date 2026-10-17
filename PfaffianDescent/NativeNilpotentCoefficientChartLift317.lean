import PfaffianDescent.NativeCommonAffineChartCover306
import PfaffianDescent.NilpotentCartesianFieldPointSupport176
import PfaffianDescent.MonomialPolynomialLocusFinitePresentation312

/-! SOURCE ONLY317. A genuine geometric classifying-map lift across a
nilpotent test reduction automatically stays in the SAME coefficient chart.
Full faithfulness306 constructs the exact original-base algebra lift.
The original-point caller must construct the geometric lift, not assume it. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Generic geometric-to-algebra conversion. The physical original open
chart and map reduction are honest inputs; no algebra lift or new chart
factor is supplied. Nilpotent reduction derives ENTIRE chart containment. -/
lemma nativeAlgebraLift_of_nilpotentOpenDiagram317
    (R : Type u) [CommRing R] {A B S : Type u}
    [CommRing A] [CommRing B] [CommRing S]
    [Algebra R A] [Algebra R B] [Algebra R S]
    {X : Scheme.{u}} (F : X ⟶ Spec (.of R))
    (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (pi : B →ₐ[R] S) (hpi : Function.Surjective pi)
    (hnil : IsNilpotent (RingHom.ker pi.toRingHom))
    (q : A →ₐ[R] S) (d : Spec (.of B) ⟶ X)
    (hd : d ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (hred : Spec.map (CommRingCat.ofHom pi.toRingHom) ≫ d =
      Spec.map (CommRingCat.ofHom q.toRingHom) ≫ j) :
    ∃ l : A →ₐ[R] B, pi.comp l = q ∧ Spec.map (CommRingCat.ofHom l.toRingHom) ≫ j = d := by
  let beta := Spec.map (CommRingCat.ofHom pi.toRingHom)
  letI : Surjective beta := surjective_specMap_of_nilpotent_kernel176 pi.toRingHom hpi hnil
  have hrange : Set.range d ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨s, rfl⟩ := beta.surjective z
    refine ⟨Spec.map (CommRingCat.ofHom q.toRingHom) s, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using
      (congrArg (fun f : Spec (.of S) ⟶ X => f s) hred).symm
  let a : Spec (.of B) ⟶ Spec (.of A) := IsOpenImmersion.lift j d hrange
  have ha : a ≫ j = d := IsOpenImmersion.lift_fac j d hrange
  have hbase : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) :=
    (congrArg (fun f => a ≫ f) hj.symm).trans
      ((Category.assoc a j F).symm.trans ((congrArg (fun f => f ≫ F) ha).trans hd))
  obtain ⟨l, hl⟩ := nativeAffineMapOverBase_algHom_exists306 R a hbase
  have hfac : Spec.map (CommRingCat.ofHom l.toRingHom) ≫ j = d :=
    (congrArg (fun f => f ≫ j) hl).trans ha
  have hspec : Spec.map (CommRingCat.ofHom pi.toRingHom) ≫
      Spec.map (CommRingCat.ofHom l.toRingHom) =
        Spec.map (CommRingCat.ofHom q.toRingHom) := by
    apply (cancel_mono j).mp
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => Spec.map (CommRingCat.ofHom pi.toRingHom) ≫ f) hfac).trans hred)
  have hcat : CommRingCat.ofHom l.toRingHom ≫ CommRingCat.ofHom pi.toRingHom =
      CommRingCat.ofHom q.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    exact hspec
  have halg : pi.comp l = q := AlgHom.ext
    (fun x => congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of S => f.hom x) hcat)
  exact ⟨l, halg, hfac⟩

private lemma nativeClosedCoefficientChart_isOpen317
    (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)
    (i : MonomialCoefficientChartIndex300 m n) :
    IsOpenImmersion (monomialClosedCoefficientChartToLocus312 R m n p i) := by
  have hcover : IsOpenImmersion
      ((monomialClosedCoefficientLocusOpenCover312 R m n p).f (.up i)) :=
    (monomialClosedCoefficientLocusOpenCover312 R m n p).map_prop (.up i)
  exact Eq.mp (congrArg (fun f => IsOpenImmersion f)
    (monomialClosedCoefficientLocusOpenCover_map312 R m n p i)) hcover

/-- SAME actual closed coefficient quotient A_i and SAME original R. Once
the genuine original-point geometric map lift is constructed, this derives
the exact chart algebra lift required by the native Artinian criterion316. -/
lemma monomialClosedCoefficientChart_lift_of_nilpotentClassifyingMap317
    (R : Type u) [CommRing R] (m n : ℕ) (p : MvPolynomial (Fin m) R)
    (i : MonomialCoefficientChartIndex300 m n)
    {B S : Type u} [CommRing B] [CommRing S] [Algebra R B] [Algebra R S]
    (pi : B →ₐ[R] S) (hpi : Function.Surjective pi)
    (hnil : IsNilpotent (RingHom.ker pi.toRingHom))
    (q : MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i →ₐ[R] S)
    (d : Spec (.of B) ⟶ monomialPolynomialContainmentLocus310 R m n p)
    (hd : d ≫ (monomialPolynomialContainmentRepresentingObject312 R m n p).hom =
      Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (hred : Spec.map (CommRingCat.ofHom pi.toRingHom) ≫ d =
      Spec.map (CommRingCat.ofHom q.toRingHom) ≫ monomialClosedCoefficientChartToLocus312 R m n p i) :
    ∃ l : MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i →ₐ[R] B,
      pi.comp l = q ∧ Spec.map (CommRingCat.ofHom l.toRingHom) ≫
        monomialClosedCoefficientChartToLocus312 R m n p i = d := by
  letI : IsOpenImmersion (monomialClosedCoefficientChartToLocus312 R m n p i) :=
    nativeClosedCoefficientChart_isOpen317 R m n p i
  exact @nativeAlgebraLift_of_nilpotentOpenDiagram317 R _
    (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i) B S
    _ _ _ _ _ _ (monomialPolynomialContainmentLocus310 R m n p)
    (monomialPolynomialContainmentRepresentingObject312 R m n p).hom
    (monomialClosedCoefficientChartToLocus312 R m n p i)
    (nativeClosedCoefficientChart_isOpen317 R m n p i)
    (monomialPolynomialContainmentChart_toBase312 R m n p i)
    pi hpi hnil q d hd hred

end PfaffianDescent
end
