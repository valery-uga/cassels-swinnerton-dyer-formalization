import AllCharacteristics.ProjectiveCoefficientParameters
import AllCharacteristics.ProjectiveSpaceChartEvaluation
import AllCharacteristics.HypersurfaceScaling
import AllCharacteristics.HypersurfaceReduction

/-!
# Transitions between normalized universal coefficient charts

Changing the distinguished coefficient divides every coefficient by an
invertible coordinate. The actual chart maps are constructed and the resulting
universal equations differ by exactly that unit. Their projective families are
therefore isomorphic after the indicated base changes, over the same base ring.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable {R A : Type u} [CommRing R] [CommRing A] {σ : Type} [Finite σ] {d : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The normalized universal equation specializes to any prescribed homogeneous
polynomial with the corresponding normalized coefficients. -/
theorem map_normalizedForm_eq (j : Monomials σ d) (f : ParameterChartRing R σ d j →+* A)
    (p : MvPolynomial σ A) (hp : p.IsHomogeneous d)
    (hc : ∀ m : Monomials σ d,
      f (chartCoordinate (ParameterIdeal R σ d) j m) = p.coeff m.1) :
    (normalizedForm R σ d j).map f = p := by
  ext m
  by_cases hm : m.degree = d
  · let n : Monomials σ d := ⟨m, hm⟩
    change ((normalizedForm R σ d j).map f).coeff n.1 = p.coeff n.1
    rw [MvPolynomial.coeff_map, normalizedForm_coeff]
    exact hc n
  · rw [((normalizedForm_isHomogeneous R σ d j).map f).coeff_eq_zero hm,
      hp.coeff_eq_zero hm]

variable (j l : Monomials σ d) (g : ParameterChartRing R σ d l →+* A)
variable (u : Aˣ) (hu : (u : A) = g (chartCoordinate (ParameterIdeal R σ d) l j))

/-- Change the distinguished coefficient from l to j wherever its value is a unit. -/
noncomputable def normalizedChartTransition : ParameterChartRing R σ d j →+* A :=
  projectiveChartMap (g.comp (chartBaseMap (ParameterIdeal R σ d) l))
    (fun m ↦ (↑(u⁻¹) : A) * g (chartCoordinate (ParameterIdeal R σ d) l m)) j (by
      rw [← hu]
      simp)

omit [Finite σ] in
/-- Coefficient-chart transition maps preserve the original coefficient base. -/
theorem normalizedChartTransition_baseMap (r : R) :
    normalizedChartTransition j l g u hu (chartBaseMap (ParameterIdeal R σ d) j r) =
      g (chartBaseMap (ParameterIdeal R σ d) l r) :=
  projectiveChartMap_baseMap _ _ _ _ r

omit [Finite σ] in
/-- Every normalized coefficient is divided by the new distinguished coordinate. -/
theorem normalizedChartTransition_coordinate (m : Monomials σ d) :
    normalizedChartTransition j l g u hu (chartCoordinate (ParameterIdeal R σ d) j m) =
      (↑(u⁻¹) : A) * g (chartCoordinate (ParameterIdeal R σ d) l m) :=
  projectiveChartMap_coordinate _ _ _ _ m

/-- The two normalized universal equations differ by the specified invertible scalar. -/
theorem map_normalizedForm_transition :
    (normalizedForm R σ d j).map (normalizedChartTransition j l g u hu) =
      C (↑(u⁻¹) : A) * (normalizedForm R σ d l).map g := by
  apply map_normalizedForm_eq j _ _ (((normalizedForm_isHomogeneous R σ d l).map g).C_mul _)
  intro m
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, normalizedForm_coeff]
  exact normalizedChartTransition_coordinate j l g u hu m

/-- Smoothness of the specialized hypersurface agrees in the two normalized charts. -/
theorem smooth_normalizedForm_transition_iff :
    Smooth (hypersurfaceToBase
      ((normalizedForm R σ d j).map (normalizedChartTransition j l g u hu))
      ((normalizedForm_isHomogeneous R σ d j).map (normalizedChartTransition j l g u hu))) ↔
    Smooth (hypersurfaceToBase ((normalizedForm R σ d l).map g)
      ((normalizedForm_isHomogeneous R σ d l).map g)) :=
  (smooth_hypersurfaceToBase_congr _ _ _ _ (map_normalizedForm_transition j l g u hu)).trans
    (smooth_hypersurfaceToBase_C_mul_iff (↑(u⁻¹) : A) (u⁻¹).isUnit _ _)

/-- The actual universal chart families agree after the prescribed base changes. -/
noncomputable def normalizedChartFamilyIso :
    pullback (normalizedFamilyToBase R σ d j)
      (Spec.map (CommRingCat.ofHom (normalizedChartTransition j l g u hu))) ≅
    pullback (normalizedFamilyToBase R σ d l) (Spec.map (CommRingCat.ofHom g)) :=
  (hypersurfaceReductionIso (normalizedChartTransition j l g u hu)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    (C (↑(u⁻¹) : A) * (normalizedForm R σ d l).map g)
    (((normalizedForm_isHomogeneous R σ d l).map g).C_mul _)
    (map_normalizedForm_transition j l g u hu)).symm ≪≫
      (hypersurfaceScalingIso (↑(u⁻¹) : A) (u⁻¹).isUnit
        ((normalizedForm R σ d l).map g) ((normalizedForm_isHomogeneous R σ d l).map g) ≪≫
        hypersurfaceBaseChangeIso g (normalizedForm R σ d l) (normalizedForm_isHomogeneous R σ d l))

/-- The chart-family identification respects the common coefficient-ring spectrum. -/
theorem normalizedChartFamilyIso_hom_snd :
    (normalizedChartFamilyIso j l g u hu).hom ≫
      pullback.snd (normalizedFamilyToBase R σ d l) (Spec.map (CommRingCat.ofHom g)) =
    pullback.snd (normalizedFamilyToBase R σ d j)
      (Spec.map (CommRingCat.ofHom (normalizedChartTransition j l g u hu))) := by
  let e := hypersurfaceReductionIso (normalizedChartTransition j l g u hu)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    (C (↑(u⁻¹) : A) * (normalizedForm R σ d l).map g)
    (((normalizedForm_isHomogeneous R σ d l).map g).C_mul _)
    (map_normalizedForm_transition j l g u hu)
  let s := hypersurfaceScalingIso (↑(u⁻¹) : A) (u⁻¹).isUnit
    ((normalizedForm R σ d l).map g) ((normalizedForm_isHomogeneous R σ d l).map g)
  let t := hypersurfaceBaseChangeIso g (normalizedForm R σ d l)
    (normalizedForm_isHomogeneous R σ d l)
  have he := e.inv_comp_eq.mpr (hypersurfaceReductionIso_hom_snd
    (normalizedChartTransition j l g u hu) (normalizedForm R σ d j)
    (normalizedForm_isHomogeneous R σ d j) _ _ (map_normalizedForm_transition j l g u hu)).symm
  have hs := hypersurfaceScalingIso_hom_toBase (↑(u⁻¹) : A) (u⁻¹).isUnit
    ((normalizedForm R σ d l).map g) ((normalizedForm_isHomogeneous R σ d l).map g)
  have ht := hypersurfaceBaseChangeIso_hom_snd g (normalizedForm R σ d l)
    (normalizedForm_isHomogeneous R σ d l)
  exact (Category.assoc e.inv (s.hom ≫ t.hom) _).trans
    ((congrArg (fun f ↦ e.inv ≫ f)
      ((Category.assoc s.hom t.hom _).trans ((congrArg (fun f ↦ s.hom ≫ f) ht).trans hs))).trans he)

end UniversalHomogeneous
end AllCharacteristics
