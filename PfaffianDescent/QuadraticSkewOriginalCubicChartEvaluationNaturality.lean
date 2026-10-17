import PfaffianDescent.QuadraticSkewOriginalCubicForwardUnitScale
import PfaffianDescent.QuadraticSkewHomogeneousChartEvaluationNaturality
/-! SOURCE ONLY / UNVERIFIED. Naturality on the entire original cubic
quadratic chart. It permits injective field evaluation to prove a ring
identity on the original inverse-domain coordinate algebra. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SecondComposite005
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective InverseChart ForwardChart004
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k A B : Type u} [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B]

theorem cubicCoordinateEvaluation_comp
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x : Fin 4 → A) (hFx : F.eval₂ (algebraMap k A) x = 0)
    (f : A →+* B) (hf : f.comp (algebraMap k A) = algebraMap k B)
    (hFy : F.eval₂ (algebraMap k B) (fun i => f (x i)) = 0) :
    f.comp (cubicCoordinateEvaluation F hF x hFx) =
      cubicCoordinateEvaluation F hF (fun i => f (x i)) hFy := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply, cubicCoordinateEvaluation_mk]
  rw [MvPolynomial.hom_eval₂, hf]

theorem forwardChartRingHom_comp
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x : Fin 4 → A) (hFx : F.eval₂ (algebraMap k A) x = 0)
    (Q : MvPolynomial (Fin 4) k) (hQx : IsUnit (Q.eval₂ (algebraMap k A) x))
    (f : A →+* B) (hf : f.comp (algebraMap k A) = algebraMap k B)
    (hFy : F.eval₂ (algebraMap k B) (fun i => f (x i)) = 0)
    (hQy : IsUnit (Q.eval₂ (algebraMap k B) (fun i => f (x i)))) :
    f.comp (forwardChartRingHom F hF x hFx Q hQx) =
      forwardChartRingHom F hF (fun i => f (x i)) hFy Q hQy := by
  unfold forwardChartRingHom
  rw [UnitChart005.liftUnit_comp]
  simp only [cubicCoordinateEvaluation_comp F hF x hFx f hf hFy]

/-- Equality in an injective field extension descends to the WHOLE
original chart map after unit-scalar reconstruction of original coordinates.
The input is a coordinate vector equality, not a scheme-map identity. -/
theorem chart_identity_of_injective_unit_reconstruction
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (x : Fin 4 → A) (hFx : F.eval₂ (algebraMap k A) x = 0)
    (Q : MvPolynomial (Fin 4) k) (hQ : Q.IsHomogeneous 2)
    (hQx : IsUnit (Q.eval₂ (algebraMap k A) x))
    (ι : QuadraticChartRing (equationIdeal F hF) Q →+* A)
    (f : A →+* B) (hfinj : Function.Injective f)
    (hf : f.comp (algebraMap k A) = algebraMap k B)
    (w : Fin 4 → B) (hFw : F.eval₂ (algebraMap k B) w = 0)
    (hQw : IsUnit (Q.eval₂ (algebraMap k B) w))
    (hcanonical : f.comp ι = forwardChartRingHom F hF w hFw Q hQw)
    (c : B) (hc : IsUnit c) (hreconstruction : (fun i => f (x i)) = c • w) :
    forwardChartRingHom F hF x hFx Q hQx = ι := by
  have hFy : F.eval₂ (algebraMap k B) (fun i => f (x i)) = 0 := by
    rw [← hf, ← MvPolynomial.hom_eval₂, hFx, map_zero]
  have hQy : IsUnit (Q.eval₂ (algebraMap k B) (fun i => f (x i))) := by
    rw [← hf, ← MvPolynomial.hom_eval₂]
    exact hQx.map f
  have hmap : f.comp (forwardChartRingHom F hF x hFx Q hQx) = f.comp ι := by
    rw [forwardChartRingHom_comp F hF x hFx Q hQx f hf hFy hQy, hcanonical]
    exact forwardChartRingHom_eq_of_unit_scale F hF w (fun i => f (x i))
      hFw hFy Q hQ hQw hQy c hc hreconstruction
  apply RingHom.ext
  intro a
  exact hfinj (RingHom.congr_fun hmap a)

end PfaffianDescent.QuadraticSkewRationality.SecondComposite005
