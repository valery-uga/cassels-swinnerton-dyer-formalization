import AllCharacteristics.UniversalProjectiveFamilyCharts
import AllCharacteristics.ProjectiveEquationParameters
import AllCharacteristics.UniversalProjectiveAmbient
import AllCharacteristics.HomogeneousClosedPoints

/-!
# Equations as fibers of the global projective universal family

Every nonzero homogeneous equation over any field is the actual fiber of the
global universal hypersurface at its projective coefficient parameter. The
identification retains the original field structure morphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable {R k : Type u} [CommRing R] [Field k] {σ : Type} [Finite σ] {d : ℕ}
variable (b : R →+* k) (p : MvPolynomial σ k)
variable (j : Monomials σ d) (hj : p.coeff j.1 ≠ 0)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The concrete map from an equation's hypersurface to the global universal
family through its normalized coefficient chart. -/
noncomputable def projectiveEquationFiberToUniversalFamily (hp : p.IsHomogeneous d) :
    hypersurface p hp ⟶ projectiveUniversalFamily R σ d :=
  projectiveEquationChartReductionMap b p j hj hp ≫ projectiveUniversalChartι R σ d j

/-- This concrete map is compatible with the ambient projective maps. -/
theorem projectiveEquationFiberToUniversalFamily_comp_toAmbient
    (hp : p.IsHomogeneous d) :
    projectiveEquationFiberToUniversalFamily b p j hj hp ≫
      projectiveUniversalToAmbient R σ d =
      hypersurfaceToAmbient p hp ≫ ambientCoefficientMap b := by
  unfold projectiveEquationFiberToUniversalFamily
  rw [Category.assoc, projectiveUniversalChartι_toAmbient,
    normalizedFamilyToAmbient,
    ← Category.assoc,
    projectiveEquationChartReductionMap_comp_hypersurfaceToAmbient,
    Category.assoc,
    ambientCoefficientMap_comp]
  have h : (projectiveEquationChartMap b p j hj).comp
      (chartBaseMap (ParameterIdeal R σ d) j) = b := by
    ext r
    exact projectiveEquationChartMap_baseMap b p j hj r
  rw [h]

/-- The concrete map to the global universal family lies over the equation's
projective coefficient parameter. -/
theorem projectiveEquationFiberToUniversalFamily_comp_toBase
    (hp : p.IsHomogeneous d) :
    projectiveEquationFiberToUniversalFamily b p j hj hp ≫
      projectiveUniversalToBase R σ d =
      hypersurfaceToBase p hp ≫ projectiveEquationParameter b p j hj := by
  unfold projectiveEquationFiberToUniversalFamily
  rw [Category.assoc, projectiveUniversalChartι_toBase,
    ← Category.assoc, projectiveEquationChartReductionMap_toBase,
    Category.assoc]
  rfl

/-- The concrete equation fiber maps into the global universal incidence
family with its expected ambient point and coefficient parameter. -/
theorem projectiveEquationFiberToUniversalFamily_comp_toIncidence
    (hp : p.IsHomogeneous d) :
    projectiveEquationFiberToUniversalFamily b p j hj hp ≫
      projectiveUniversalIncidence R σ d =
      Limits.prod.lift
        (hypersurfaceToAmbient p hp ≫ ambientCoefficientMap b)
        (hypersurfaceToBase p hp ≫ projectiveEquationParameter b p j hj) := by
  apply Limits.prod.hom_ext
  · rw [Category.assoc, projectiveUniversalIncidence_fst, Limits.prod.lift_fst]
    exact projectiveEquationFiberToUniversalFamily_comp_toAmbient b p j hj hp
  · rw [Category.assoc, projectiveUniversalIncidence_snd, Limits.prod.lift_snd]
    exact projectiveEquationFiberToUniversalFamily_comp_toBase b p j hj hp

/-- A concrete point of a nonzero homogeneous hypersurface belongs to the
universal incidence locus at its equation's projective parameter. -/
theorem projectiveEquationIncidence_mem_range (hp : p.IsHomogeneous d)
    (x : hypersurface p hp) :
    Limits.prod.lift
      (hypersurfaceToAmbient p hp ≫ ambientCoefficientMap b)
      (hypersurfaceToBase p hp ≫ projectiveEquationParameter b p j hj) x ∈
      Set.range (projectiveUniversalIncidence R σ d) := by
  refine ⟨projectiveEquationFiberToUniversalFamily b p j hj hp x, ?_⟩
  rw [← Scheme.Hom.comp_apply]
  exact congrArg (fun f ↦ f x)
    (projectiveEquationFiberToUniversalFamily_comp_toIncidence b p j hj hp)

/-- A point of a normalized universal coefficient chart gives a nonzero
residue-field solution of its specialized equation.  The specialized equation
is itself nonzero because its distinguished coefficient remains one. -/
theorem normalizedForm_residueField_coordinates (j : Monomials σ d)
    (x : hypersurface (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)) :
    letI := pointAlgebraOf (normalizedFamilyToBase R σ d j) x
    ∃ v : σ → (hypersurface (normalizedForm R σ d j)
        (normalizedForm_isHomogeneous R σ d j)).residueField x,
      v ≠ 0 ∧
        ((normalizedForm R σ d j).map (algebraMap (ParameterChartRing R σ d j)
          ((hypersurface (normalizedForm R σ d j)
            (normalizedForm_isHomogeneous R σ d j)).residueField x))).eval v = 0 ∧
        (normalizedForm R σ d j).map (algebraMap (ParameterChartRing R σ d j)
          ((hypersurface (normalizedForm R σ d j)
            (normalizedForm_isHomogeneous R σ d j)).residueField x)) ≠ 0 := by
  let := pointAlgebraOf (normalizedFamilyToBase R σ d j) x
  obtain ⟨v, hv, he⟩ := hypersurface_coordinates_of_point
    (algebraMap (ParameterChartRing R σ d j)
      ((hypersurface (normalizedForm R σ d j)
        (normalizedForm_isHomogeneous R σ d j)).residueField x))
    (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)
    ((hypersurface (normalizedForm R σ d j)
      (normalizedForm_isHomogeneous R σ d j)).fromSpecResidueField x)
    (pointAlgebraOf_spec (normalizedFamilyToBase R σ d j) x).symm
  refine ⟨v, hv, ?_, normalizedForm_map_ne_zero R σ d j _⟩
  simpa only [MvPolynomial.eval₂_eq_eval_map] using he

/-- Every point of the glued universal family occurs in a normalized chart,
whose equation has a nonzero residue-field solution. -/
theorem exists_normalizedForm_residueField_coordinates
    (x : projectiveUniversalFamily R σ d) :
    ∃ (j : Monomials σ d)
      (y : hypersurface (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)),
      projectiveUniversalChartι R σ d j y = x ∧
      letI := pointAlgebraOf (normalizedFamilyToBase R σ d j) y
      ∃ v : σ → (hypersurface (normalizedForm R σ d j)
          (normalizedForm_isHomogeneous R σ d j)).residueField y,
        v ≠ 0 ∧
          ((normalizedForm R σ d j).map (algebraMap (ParameterChartRing R σ d j)
            ((hypersurface (normalizedForm R σ d j)
              (normalizedForm_isHomogeneous R σ d j)).residueField y))).eval v = 0 ∧
          (normalizedForm R σ d j).map (algebraMap (ParameterChartRing R σ d j)
            ((hypersurface (normalizedForm R σ d j)
              (normalizedForm_isHomogeneous R σ d j)).residueField y)) ≠ 0 := by
  obtain ⟨j, y, hy⟩ := projectiveUniversalChartι_jointly_surjective R σ d x
  exact ⟨j, y, hy, normalizedForm_residueField_coordinates j y⟩

/-- A field-valued point of the glued universal family lifts to one normalized
coefficient chart.  The lift is a morphism, not merely an equality of its
closed carrier point. -/
theorem exists_normalizedForm_fieldPoint
    {L : Type u} [Field L]
    (q : Spec (.of L) ⟶ projectiveUniversalFamily R σ d) :
    ∃ (j : Monomials σ d)
      (qj : Spec (.of L) ⟶ hypersurface (normalizedForm R σ d j)
        (normalizedForm_isHomogeneous R σ d j)),
      qj ≫ projectiveUniversalChartι R σ d j = q := by
  obtain ⟨j, y, hy⟩ := projectiveUniversalChartι_jointly_surjective R σ d
    (q (IsLocalRing.closedPoint L))
  have hqrange : Set.range q ⊆ Set.range (projectiveUniversalChartι R σ d j) := by
    rintro x ⟨t, rfl⟩
    have ht : t = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    subst t
    exact ⟨y, hy⟩
  refine ⟨j, IsOpenImmersion.lift (projectiveUniversalChartι R σ d j) q hqrange, ?_⟩
  exact IsOpenImmersion.lift_fac _ _ _

/-- Finitely many field-valued points of the glued universal family over one
coefficient-parameter point lift through one common normalized coefficient
chart.  In particular, their specialized normalized equations are defined
over one field and one coefficient homomorphism. -/
theorem exists_normalizedForm_fieldPoints_of_common_base
    {L : Type u} [Field L] {n : ℕ}
    (q : Fin n → (Spec (.of L) ⟶ projectiveUniversalFamily R σ d))
    (t : Spec (.of L) ⟶ projectiveParameters R σ d)
    (ht : ∀ i, q i ≫ projectiveUniversalToBase R σ d = t) :
    ∃ (j : Monomials σ d)
      (u : Spec (.of L) ⟶ Spec (.of (ParameterChartRing R σ d j)))
      (qj : Fin n → (Spec (.of L) ⟶ hypersurface (normalizedForm R σ d j)
        (normalizedForm_isHomogeneous R σ d j))),
      u ≫ parameterChartι R σ d j = t ∧
        (∀ i, qj i ≫ projectiveUniversalChartι R σ d j = q i) ∧
        ∀ i, qj i ≫ normalizedFamilyToBase R σ d j = u := by
  obtain ⟨j, y, hy⟩ := exists_coordinate_chart (ParameterIdeal R σ d)
    (t (IsLocalRing.closedPoint L))
  have htrange : Set.range t ⊆ Set.range (parameterChartι R σ d j) := by
    rintro x ⟨v, rfl⟩
    have hv : v = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    subst v
    exact ⟨y, hy⟩
  let u : Spec (.of L) ⟶ Spec (.of (ParameterChartRing R σ d j)) :=
    IsOpenImmersion.lift (parameterChartι R σ d j) t htrange
  have hu : u ≫ parameterChartι R σ d j = t :=
    IsOpenImmersion.lift_fac _ _ _
  let H := isPullback_projectiveUniversalChart R σ d j
  refine ⟨j, u, fun i ↦ H.lift (q i) u ((ht i).trans hu.symm), hu, ?_, ?_⟩
  · intro i
    exact H.lift_fst (q i) u ((ht i).trans hu.symm)
  · intro i
    exact H.lift_snd (q i) u ((ht i).trans hu.symm)

/-- Membership in the global universal incidence range can be unpacked into
a normalized chart equation with a nonzero residue-field solution.  The
first conjunct retains the exact ambient point and coefficient parameter of
the original incidence witness. -/
theorem exists_normalizedForm_residueField_coordinates_of_mem_range
    {z : (Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d : Scheme.{u})}
    (hz : z ∈ Set.range (projectiveUniversalIncidence R σ d)) :
    ∃ (j : Monomials σ d)
      (y : hypersurface (normalizedForm R σ d j) (normalizedForm_isHomogeneous R σ d j)),
      Limits.prod.lift (normalizedFamilyToAmbient R σ d j)
        (normalizedFamilyToBase R σ d j ≫ parameterChartι R σ d j) y = z ∧
      letI := pointAlgebraOf (normalizedFamilyToBase R σ d j) y
      ∃ v : σ → (hypersurface (normalizedForm R σ d j)
          (normalizedForm_isHomogeneous R σ d j)).residueField y,
        v ≠ 0 ∧
          ((normalizedForm R σ d j).map (algebraMap (ParameterChartRing R σ d j)
            ((hypersurface (normalizedForm R σ d j)
              (normalizedForm_isHomogeneous R σ d j)).residueField y))).eval v = 0 ∧
          (normalizedForm R σ d j).map (algebraMap (ParameterChartRing R σ d j)
            ((hypersurface (normalizedForm R σ d j)
              (normalizedForm_isHomogeneous R σ d j)).residueField y)) ≠ 0 := by
  obtain ⟨x, hx⟩ := hz
  obtain ⟨j, y, hy, hv⟩ := exists_normalizedForm_residueField_coordinates x
  refine ⟨j, y, ?_, hv⟩
  have hchart := congrArg (fun f ↦ f y) (projectiveUniversalChartι_toIncidence R σ d j)
  calc
    Limits.prod.lift (normalizedFamilyToAmbient R σ d j)
        (normalizedFamilyToBase R σ d j ≫ parameterChartι R σ d j) y =
        projectiveUniversalIncidence R σ d (projectiveUniversalChartι R σ d j y) := hchart.symm
    _ = projectiveUniversalIncidence R σ d x := congrArg (projectiveUniversalIncidence R σ d) hy
    _ = z := hx

/-- The normalized chart fiber is also the fiber of the global family at the
equation's projective parameter. -/
theorem isPullback_globalFamily_equationParameter :
    IsPullback
      (pullback.fst (normalizedFamilyToBase R σ d j)
        (Spec.map (CommRingCat.ofHom (projectiveEquationChartMap b p j hj))) ≫
          projectiveUniversalChartι R σ d j)
      (pullback.snd (normalizedFamilyToBase R σ d j)
        (Spec.map (CommRingCat.ofHom (projectiveEquationChartMap b p j hj))))
      (projectiveUniversalToBase R σ d) (projectiveEquationParameter b p j hj) :=
  (IsPullback.of_hasPullback (normalizedFamilyToBase R σ d j)
    (Spec.map (CommRingCat.ofHom (projectiveEquationChartMap b p j hj)))).paste_horiz
      (isPullback_projectiveUniversalChart R σ d j)

/-- The original hypersurface is the actual fiber of the global universal family. -/
noncomputable def projectiveEquationFiberIso (hp : p.IsHomogeneous d) :
    hypersurface p hp ≅ pullback (projectiveUniversalToBase R σ d)
      (projectiveEquationParameter b p j hj) :=
  projectiveEquationChartFiberIso b p j hj hp ≪≫
    (isPullback_globalFamily_equationParameter b p j hj).isoPullback

/-- The global fiber identification preserves the original coefficient field. -/
theorem projectiveEquationFiberIso_hom_snd (hp : p.IsHomogeneous d) :
    (projectiveEquationFiberIso b p j hj hp).hom ≫
      pullback.snd (projectiveUniversalToBase R σ d) (projectiveEquationParameter b p j hj) =
        hypersurfaceToBase p hp := by
  change ((projectiveEquationChartFiberIso b p j hj hp).hom ≫
    (isPullback_globalFamily_equationParameter b p j hj).isoPullback.hom) ≫ _ = _
  rw [Category.assoc, IsPullback.isoPullback_hom_snd]
  exact projectiveEquationChartFiberIso_hom_snd b p j hj hp

/-- The first projection of the global fiber isomorphism is the concrete
map from the specified hypersurface into the universal family. -/
theorem projectiveEquationFiberIso_hom_fst (hp : p.IsHomogeneous d) :
    (projectiveEquationFiberIso b p j hj hp).hom ≫
      pullback.fst (projectiveUniversalToBase R σ d)
        (projectiveEquationParameter b p j hj) =
      projectiveEquationFiberToUniversalFamily b p j hj hp := by
  change ((projectiveEquationChartFiberIso b p j hj hp).hom ≫
      (isPullback_globalFamily_equationParameter b p j hj).isoPullback.hom) ≫
        pullback.fst (projectiveUniversalToBase R σ d)
          (projectiveEquationParameter b p j hj) = _
  rw [Category.assoc, IsPullback.isoPullback_hom_fst]
  rw [← Category.assoc, projectiveEquationChartFiberIso_hom_fst]
  rfl

/-- Every nonzero homogeneous equation over any field occurs as an actual
fiber of the global projective universal family, over that same field. -/
theorem exists_projectiveEquationFiber (hp : p.IsHomogeneous d) (hne : p ≠ 0) :
    ∃ (s : Spec (.of k) ⟶ projectiveParameters R σ d)
      (e : hypersurface p hp ≅ pullback (projectiveUniversalToBase R σ d) s),
      s ≫ projectiveParametersToBase R σ d = Spec.map (CommRingCat.ofHom b) ∧
        e.hom ≫ pullback.snd (projectiveUniversalToBase R σ d) s = hypersurfaceToBase p hp := by
  obtain ⟨i, hi⟩ := homogeneous_exists_nonzero_coefficient p hp hne
  exact ⟨projectiveEquationParameter b p i hi, projectiveEquationFiberIso b p i hi hp,
    projectiveEquationParameter_toBase b p i hi, projectiveEquationFiberIso_hom_snd b p i hi hp⟩

end UniversalHomogeneous
end AllCharacteristics
