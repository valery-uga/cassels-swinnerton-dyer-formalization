import AllCharacteristics.HypersurfaceFiberComparison
import AllCharacteristics.NormalizedCoefficientCocycle
import AllCharacteristics.UniversalCoefficientOverlap

/-!
# Composition of the actual normalized family isomorphisms

The reduction-and-scaling family isomorphisms are the canonical comparisons
of equal specialized ideals. Successive normalization therefore composes to
direct normalization, with the explicit transport along the proved equality
of coefficient homomorphisms. This holds over every commutative overlap ring.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace HomogeneousProjective
variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A] {σ : Type} {d : ℕ}

/-- Changing a coefficient homomorphism by a proved equality transports the
source fiber and leaves its canonical comparison unchanged. -/
theorem hypersurfaceFiberComparison_congr_left (b b' : R →+* A)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d)
    (c : S →+* A) (q : MvPolynomial σ S) (hq : q.IsHomogeneous d)
    (h : equationIdeal (p.map b) (hp.map b) = equationIdeal (q.map c) (hq.map c))
    (h' : equationIdeal (p.map b') (hp.map b') = equationIdeal (q.map c) (hq.map c))
    (hb : b = b') :
    hypersurfaceFiberComparison b p hp c q hq h =
      eqToIso (congrArg (fun f : R →+* A ↦
        pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom f))) hb) ≪≫
      hypersurfaceFiberComparison b' p hp c q hq h' := by
  subst b'
  simp

end HomogeneousProjective

namespace UniversalHomogeneous
open HomogeneousProjective
variable {R A : Type u} [CommRing R] [CommRing A] {σ : Type} [Finite σ] {d : ℕ}

/-- The previously defined normalized chart-family isomorphism is the canonical
comparison of its specialized homogeneous ideals. -/
theorem normalizedChartFamilyIso_eq_fiberComparison (j l : Monomials σ d)
    (g : ParameterChartRing R σ d l →+* A) (u : Aˣ)
    (hu : (u : A) = g (chartCoordinate (ParameterIdeal R σ d) l j)) :
    normalizedChartFamilyIso j l g u hu =
      hypersurfaceFiberComparison (normalizedChartTransition j l g u hu)
        (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
        g (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)
        (equationIdeal_eq_of_unit_multiple _ _ _ _ (↑(u⁻¹) : A) (u⁻¹).isUnit
          (map_normalizedForm_transition j l g u hu)) :=
  (hypersurfaceFiberComparison_eq_reduction_scaling _ _ _ _ _ _ _ _ _).symm

/-- The actual projective chart-overlap isomorphism has the same canonical comparison form. -/
theorem normalizedOverlapFamilyIso_eq_fiberComparison (j l : Monomials σ d) :
    normalizedOverlapFamilyIso R σ d j l =
      hypersurfaceFiberComparison (chartOverlapLeftMap (ParameterIdeal R σ d) j l)
        (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
        (chartOverlapRightMap (ParameterIdeal R σ d) j l)
        (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)
        (equationIdeal_eq_of_unit_multiple _ _ _ _
          (↑((chartOverlapUnit (ParameterIdeal R σ d) j l)⁻¹) :
            ChartOverlapRing (ParameterIdeal R σ d) j l)
          ((chartOverlapUnit (ParameterIdeal R σ d) j l)⁻¹).isUnit
          (normalizedForm_overlap_relation R σ d j l)) :=
  (hypersurfaceFiberComparison_eq_reduction_scaling _ _ _ _ _ _ _ _ _).symm

/-- The actual family isomorphisms satisfy the normalization cocycle over any
common coefficient ring, with transport along the coefficient-map composition law. -/
theorem normalizedChartFamilyIso_comp (i j l : Monomials σ d)
    (g : ParameterChartRing R σ d l →+* A) (u : Aˣ)
    (hu : (u : A) = g (chartCoordinate (ParameterIdeal R σ d) l j)) (v : Aˣ)
    (hv : (v : A) = normalizedChartTransition j l g u hu
      (chartCoordinate (ParameterIdeal R σ d) j i)) :
    normalizedChartFamilyIso i j (normalizedChartTransition j l g u hu) v hv ≪≫
      normalizedChartFamilyIso j l g u hu =
    eqToIso (congrArg (fun f : ParameterChartRing R σ d i →+* A ↦
      pullback (normalizedFamilyToBase R σ d i) (Spec.map (CommRingCat.ofHom f)))
        (normalizedChartTransition_comp i j l g u hu v hv)) ≪≫
      normalizedChartFamilyIso i l g (v * u)
        (normalizedChartTransition_compositeUnit i j l g u hu v hv) := by
  simp only [normalizedChartFamilyIso_eq_fiberComparison]
  let fj := normalizedChartTransition j l g u hu
  let fi := normalizedChartTransition i j fj v hv
  let fi' := normalizedChartTransition i l g (v * u)
    (normalizedChartTransition_compositeUnit i j l g u hu v hv)
  let hij := equationIdeal_eq_of_unit_multiple _ _
    ((normalizedForm_isHomogeneous R σ d i).map fi)
    ((normalizedForm_isHomogeneous R σ d j).map fj) (↑(v⁻¹) : A) (v⁻¹).isUnit
    (map_normalizedForm_transition i j fj v hv)
  let hjl := equationIdeal_eq_of_unit_multiple _ _
    ((normalizedForm_isHomogeneous R σ d j).map fj)
    ((normalizedForm_isHomogeneous R σ d l).map g) (↑(u⁻¹) : A) (u⁻¹).isUnit
    (map_normalizedForm_transition j l g u hu)
  let hil := equationIdeal_eq_of_unit_multiple _ _
    ((normalizedForm_isHomogeneous R σ d i).map fi')
    ((normalizedForm_isHomogeneous R σ d l).map g) (↑((v * u)⁻¹) : A) ((v * u)⁻¹).isUnit
    (map_normalizedForm_transition i l g (v * u)
      (normalizedChartTransition_compositeUnit i j l g u hu v hv))
  have hc := hypersurfaceFiberComparison_comp fi
    (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)
    fj (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    g (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l) hij hjl
  have he := hypersurfaceFiberComparison_congr_left fi fi'
    (normalizedForm R σ d i) (normalizedForm_isHomogeneous R σ d i)
    g (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l)
    (hij.trans hjl) hil (normalizedChartTransition_comp i j l g u hu v hv)
  exact hc.trans he

end UniversalHomogeneous
end AllCharacteristics
