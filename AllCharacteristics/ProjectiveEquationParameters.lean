import AllCharacteristics.NormalizedCoefficientTransitions
import AllCharacteristics.HypersurfaceCoefficientNaturality

/-!
# Field-valued equations in projective coefficient charts

Every nonzero homogeneous equation has a nonzero coefficient, hence defines a
point of a normalized projective coefficient chart. The actual hypersurface is
identified with the chart family's fiber, over the given field and without
any perfection, separability, or characteristic restriction.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable {R k : Type u} [CommRing R] [Field k] {σ : Type} {d : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonzero homogeneous equation has a nonzero coefficient of its prescribed degree. -/
theorem homogeneous_exists_nonzero_coefficient (p : MvPolynomial σ k)
    (hp : p.IsHomogeneous d) (hne : p ≠ 0) :
    ∃ j : Monomials σ d, p.coeff j.1 ≠ 0 := by
  by_contra! h
  apply hne
  ext m
  by_cases hm : m.degree = d
  · simpa only [MvPolynomial.coeff_zero] using h ⟨m, hm⟩
  · simpa only [MvPolynomial.coeff_zero] using hp.coeff_eq_zero hm

variable (b : R →+* k) (p : MvPolynomial σ k)
variable (j : Monomials σ d) (hj : p.coeff j.1 ≠ 0)

/-- The normalized coefficient map of an equation with a chosen nonzero coefficient. -/
noncomputable def projectiveEquationChartMap : ParameterChartRing R σ d j →+* k :=
  projectiveChartMap b (fun m : Monomials σ d ↦ (p.coeff j.1)⁻¹ * p.coeff m.1) j
    (inv_mul_cancel₀ hj)

/-- The normalized equation parameter retains the original coefficient-field map. -/
theorem projectiveEquationChartMap_baseMap (r : R) :
    projectiveEquationChartMap b p j hj (chartBaseMap (ParameterIdeal R σ d) j r) = b r :=
  projectiveChartMap_baseMap _ _ _ _ r

/-- Its normalized coefficient is the ratio of the original equation coefficients. -/
theorem projectiveEquationChartMap_coordinate (m : Monomials σ d) :
    projectiveEquationChartMap b p j hj (chartCoordinate (ParameterIdeal R σ d) j m) =
      (p.coeff j.1)⁻¹ * p.coeff m.1 :=
  projectiveChartMap_coordinate _ _ _ _ m

variable [Finite σ]

/-- The normalized universal equation recovers the original equation up to its
specified nonzero scalar. -/
theorem map_normalizedForm_equationChart (hp : p.IsHomogeneous d) :
    (normalizedForm R σ d j).map (projectiveEquationChartMap b p j hj) =
      C (p.coeff j.1)⁻¹ * p := by
  apply map_normalizedForm_eq j _ _ (hp.C_mul _)
  intro m
  rw [MvPolynomial.coeff_C_mul]
  exact projectiveEquationChartMap_coordinate b p j hj m

/-- The actual field-valued projective coefficient parameter of the equation. -/
noncomputable def projectiveEquationParameter : Spec (.of k) ⟶ projectiveParameters R σ d :=
  Spec.map (CommRingCat.ofHom (projectiveEquationChartMap b p j hj)) ≫ parameterChartι R σ d j

omit [Finite σ] in
/-- The projective coefficient parameter is over the original coefficient base. -/
theorem projectiveEquationParameter_toBase :
    projectiveEquationParameter b p j hj ≫ projectiveParametersToBase R σ d =
      Spec.map (CommRingCat.ofHom b) := by
  rw [projectiveEquationParameter, Category.assoc, parameterChartι_toBase, ← Spec.map_comp]
  have h : (projectiveEquationChartMap b p j hj).comp
      (chartBaseMap (ParameterIdeal R σ d) j) = b := by
    ext r
    exact projectiveEquationChartMap_baseMap b p j hj r
  exact congrArg (fun f : R →+* k ↦ Spec.map (CommRingCat.ofHom f)) h

/-- The original hypersurface is the actual fiber of the normalized chart family. -/
noncomputable def projectiveEquationChartFiberIso (hp : p.IsHomogeneous d) :
    hypersurface p hp ≅ pullback (normalizedFamilyToBase R σ d j)
      (Spec.map (CommRingCat.ofHom (projectiveEquationChartMap b p j hj))) :=
  (hypersurfaceScalingIso (p.coeff j.1)⁻¹
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hj)) p hp).symm ≪≫
    hypersurfaceReductionIso (projectiveEquationChartMap b p j hj)
      (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
      (C (p.coeff j.1)⁻¹ * p) (hp.C_mul _)
      (map_normalizedForm_equationChart b p j hj hp)

/-- The concrete map from an equation's hypersurface to the normalized
universal chart hypersurface at its coefficient specialization. -/
noncomputable def projectiveEquationChartReductionMap (hp : p.IsHomogeneous d) :
    hypersurface p hp ⟶
      hypersurface (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j) :=
  (hypersurfaceScalingIso (p.coeff j.1)⁻¹
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hj)) p hp).inv ≫
    hypersurfaceReductionMap (projectiveEquationChartMap b p j hj)
      (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
      (C (p.coeff j.1)⁻¹ * p) (hp.C_mul _)
      (map_normalizedForm_equationChart b p j hj hp)

/-- The first projection of the chart-fiber isomorphism is the concrete
reduction map through the normalized chart. -/
theorem projectiveEquationChartFiberIso_hom_fst (hp : p.IsHomogeneous d) :
    (projectiveEquationChartFiberIso b p j hj hp).hom ≫
      pullback.fst (normalizedFamilyToBase R σ d j)
        (Spec.map (CommRingCat.ofHom (projectiveEquationChartMap b p j hj))) =
      projectiveEquationChartReductionMap b p j hj hp := by
  change ((hypersurfaceScalingIso (p.coeff j.1)⁻¹
      (isUnit_iff_ne_zero.mpr (inv_ne_zero hj)) p hp).inv ≫
    (hypersurfaceReductionIso (projectiveEquationChartMap b p j hj)
      (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
      (C (p.coeff j.1)⁻¹ * p) (hp.C_mul _)
      (map_normalizedForm_equationChart b p j hj hp)).hom) ≫ _ = _
  exact Category.assoc _ _ _

/-- The normalized-chart reduction map is compatible with the ambient
projective maps. -/
theorem projectiveEquationChartReductionMap_comp_hypersurfaceToAmbient
    (hp : p.IsHomogeneous d) :
    projectiveEquationChartReductionMap b p j hj hp ≫
      hypersurfaceToAmbient (normalizedForm R σ d j)
        (normalizedForm_isHomogeneous R σ d j) =
      hypersurfaceToAmbient p hp ≫
        ambientCoefficientMap (projectiveEquationChartMap b p j hj) := by
  unfold projectiveEquationChartReductionMap
  rw [Category.assoc,
    hypersurfaceReductionMap_comp_hypersurfaceToAmbient,
    ← Category.assoc,
    hypersurfaceScalingIso_inv_comp_hypersurfaceToAmbient,
    Category.assoc,
    ambientCoefficientMap_comp]
  rfl

/-- The fiber identification preserves the original field structure morphism. -/
theorem projectiveEquationChartFiberIso_hom_snd (hp : p.IsHomogeneous d) :
    (projectiveEquationChartFiberIso b p j hj hp).hom ≫
      pullback.snd (normalizedFamilyToBase R σ d j)
        (Spec.map (CommRingCat.ofHom (projectiveEquationChartMap b p j hj))) =
      hypersurfaceToBase p hp := by
  let e := hypersurfaceScalingIso (p.coeff j.1)⁻¹
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hj)) p hp
  let t := hypersurfaceReductionIso (projectiveEquationChartMap b p j hj)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    (C (p.coeff j.1)⁻¹ * p) (hp.C_mul _)
    (map_normalizedForm_equationChart b p j hj hp)
  have he := e.inv_comp_eq.mpr (hypersurfaceScalingIso_hom_toBase (p.coeff j.1)⁻¹
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hj)) p hp).symm
  have ht := hypersurfaceReductionIso_hom_snd (projectiveEquationChartMap b p j hj)
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    (C (p.coeff j.1)⁻¹ * p) (hp.C_mul _)
    (map_normalizedForm_equationChart b p j hj hp)
  exact (Category.assoc e.inv t.hom _).trans ((congrArg (fun f ↦ e.inv ≫ f) ht).trans he)

/-- The normalized-chart reduction map lies over the coefficient
specialization defining the chart point. -/
theorem projectiveEquationChartReductionMap_toBase (hp : p.IsHomogeneous d) :
    projectiveEquationChartReductionMap b p j hj hp ≫
      normalizedFamilyToBase R σ d j =
      hypersurfaceToBase p hp ≫
        Spec.map (CommRingCat.ofHom (projectiveEquationChartMap b p j hj)) := by
  rw [← projectiveEquationChartFiberIso_hom_fst b p j hj hp,
    Category.assoc, pullback.condition, ← Category.assoc,
    projectiveEquationChartFiberIso_hom_snd]

end UniversalHomogeneous
end AllCharacteristics
