import PfaffianDescent.SchemeModuleParameterizedSection
import PfaffianDescent.VoisinFixedLinearSystemParameters
import PfaffianDescent.LinearNormalizedProjectivePoint
import AllCharacteristics.ProjectivePointCoordinates
import AllCharacteristics.ProjectiveSpaceCharts

/-!
# Normalized charts of a projective section system

On the standard chart of the projective space of `H⁰(M)` where the `j`th
coordinate is nonzero, normalize that coordinate to one.  Pull the resulting
regular coefficient functions to the fibre product with the underlying
scheme and form their finite linear combination of a chosen basis of global
sections.  These are the local universal sections whose zero schemes glue to
the universal divisor.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

universe u

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous ideal defining the projective space of a
finite-dimensional vector space. -/
noncomputable abbrev finiteDimensionalProjectiveIdeal
    (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] :
    HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule (Fin (Module.finrank K V)) K) := ⊥

/-- Coordinate ring of one normalized chart of the projective section
space. -/
abbrev finiteDimensionalProjectiveChartRing
    (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (j : Fin (Module.finrank K V)) :=
  ChartRing (finiteDimensionalProjectiveIdeal K V) j

/-- One standard affine chart of the projective section parameter space. -/
noncomputable abbrev finiteDimensionalProjectiveChart
    (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (j : Fin (Module.finrank K V)) : Scheme.{u} :=
  Spec (.of (finiteDimensionalProjectiveChartRing K V j))

/-- Inclusion of a normalized chart into the projective section space. -/
noncomputable def finiteDimensionalProjectiveChartι
    (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (j : Fin (Module.finrank K V)) :
    finiteDimensionalProjectiveChart K V j ⟶
      finiteDimensionalProjectiveParameters K V :=
  chartι (finiteDimensionalProjectiveIdeal K V) j

instance finiteDimensionalProjectiveChartι_isOpenImmersion
    (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (j : Fin (Module.finrank K V)) :
    IsOpenImmersion (finiteDimensionalProjectiveChartι K V j) := by
  unfold finiteDimensionalProjectiveChartι
  infer_instance

/-- Structure morphism of a normalized projective-section chart. -/
noncomputable def finiteDimensionalProjectiveChartToBase
    (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (j : Fin (Module.finrank K V)) :
    finiteDimensionalProjectiveChart K V j ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom
    (chartBaseMap (finiteDimensionalProjectiveIdeal K V) j))

/-- The chart inclusion respects the projective-space structure morphism. -/
theorem finiteDimensionalProjectiveChartι_toBase
    (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (j : Fin (Module.finrank K V)) :
    finiteDimensionalProjectiveChartι K V j ≫
        finiteDimensionalProjectiveParametersToBase K V =
      finiteDimensionalProjectiveChartToBase K V j := by
  exact chartι_toBase (finiteDimensionalProjectiveIdeal K V) j

/-- A field-valued point of the finite-dimensional projective parameter
space factors through one normalized coordinate chart.  The resulting
chart-ring homomorphism lies over the specified coefficient-field map and
reconstructs the original projective point. -/
theorem exists_finiteDimensionalProjectiveChart_hom_eq_of_fieldPoint
    {K L V : Type u} [Field K] [Field L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (g : K →+* L)
    (t : Spec (.of L) ⟶ finiteDimensionalProjectiveParameters K V)
    (ht : t ≫ finiteDimensionalProjectiveParametersToBase K V =
      Spec.map (CommRingCat.ofHom g)) :
    ∃ j : Fin (Module.finrank K V),
      ∃ b : finiteDimensionalProjectiveChartRing K V j →+* L,
        b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K V) j) = g ∧
        Spec.map (CommRingCat.ofHom b) ≫
          finiteDimensionalProjectiveChartι K V j = t := by
  exact exists_chart_hom_eq_of_point
    (finiteDimensionalProjectiveIdeal K V) g t ht

/-- Evaluating all normalized coordinate functions at a field-valued point
of one standard chart gives a nonzero coordinate vector. -/
theorem finiteDimensionalProjectiveChart_coordinates_ne_zero
    {K L V : Type u} [Field K] [Field L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (j : Fin (Module.finrank K V))
    (b : finiteDimensionalProjectiveChartRing K V j →+* L) :
    (fun i : Fin (Module.finrank K V) =>
      b (chartCoordinate (finiteDimensionalProjectiveIdeal K V) j i)) ≠ 0 := by
  intro hzero
  have hj := congrFun hzero j
  rw [chartCoordinate_self, map_one, Pi.zero_apply] at hj
  exact one_ne_zero hj

/-- A nonzero extension-field coordinate vector gives a projective parameter
together with a chart presentation retaining its exact normalized
coordinates.  The earlier existence theorem records only the structure map;
this strengthened form is what identifies the local universal section with
the original scalar-extended section up to the nonzero scalar `c j`. -/
theorem exists_finiteDimensionalProjectiveParameter_normalized_of_ne_zero
    {K L V : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (c : Fin (Module.finrank K V) → L) (hc : c ≠ 0) :
    ∃ (j : Fin (Module.finrank K V))
      (b : finiteDimensionalProjectiveChartRing K V j →+* L)
      (t : Spec (.of L) ⟶ finiteDimensionalProjectiveParameters K V),
      c j ≠ 0 ∧
      b.comp (chartBaseMap (finiteDimensionalProjectiveIdeal K V) j) =
        algebraMap K L ∧
      Spec.map (CommRingCat.ofHom b) ≫
        finiteDimensionalProjectiveChartι K V j = t ∧
      (∀ i, b (chartCoordinate
        (finiteDimensionalProjectiveIdeal K V) j i) = (c j)⁻¹ * c i) ∧
      t ≫ finiteDimensionalProjectiveParametersToBase K V =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  let I := finiteDimensionalProjectiveIdeal K V
  let x : Fin (Module.finrank K V) → L := fun i => (c j)⁻¹ * c i
  have hxj : x j = 1 := by
    dsimp [x]
    exact inv_mul_cancel₀ hj
  have he : ∀ p ∈ I.toIdeal,
      (MvPolynomial.eval₂Hom (algebraMap K L) x) p = 0 := by
    intro p hp
    have hp0 : p = 0 := by simpa [I] using hp
    subst p
    simp
  let z := coordinate I j
  have hz : z ∈ grading I 1 := coordinate_mem I j
  have hzOne : (Ideal.Quotient.lift I.toIdeal
      (MvPolynomial.eval₂Hom (algebraMap K L) x) he) z = 1 := by
    dsimp only [z, coordinate]
    rw [Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X']
    exact hxj
  let b := linearNormalizedPointChartMapAt I x he z hz hzOne
  let t := linearNormalizedPointAt I x he z hz hzOne
  refine ⟨j, b, t, hj, ?_, rfl, ?_, ?_⟩
  · apply RingHom.ext
    intro r
    exact linearNormalizedPointChartMapAt_base I x he z hz hzOne r
  · intro i
    exact linearNormalizedPointChartMapAt_coordinate I x he z hz hzOne i
  · exact linearNormalizedPointAt_toBase I x he z hz hzOne

/-- A chart-ring point whose coefficient map is `g` is a scheme point over
`Spec g`.  This is the morphism form of the ring-homomorphism compatibility
returned by the normalized-parameter construction. -/
theorem finiteDimensionalProjectiveChart_specMap_toBase
    {K L V : Type u} [Field K] [Field L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (j : Fin (Module.finrank K V))
    (b : finiteDimensionalProjectiveChartRing K V j →+* L)
    (g : K →+* L)
    (hb : b.comp (chartBaseMap
      (finiteDimensionalProjectiveIdeal K V) j) = g) :
    Spec.map (CommRingCat.ofHom b) ≫
        finiteDimensionalProjectiveChartToBase K V j =
      Spec.map (CommRingCat.ofHom g) := by
  unfold finiteDimensionalProjectiveChartToBase
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hb

/-- The surface over one normalized section-parameter chart. -/
noncomputable abbrev schemeModuleProjectiveSectionChartAmbient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    Scheme.{u} :=
  pullback base
    (finiteDimensionalProjectiveChartToBase K
      (SchemeModuleGlobalSectionsOver base M) j)

/-- The surface over one parameter chart maps to the surface over the full
projective section space by base change of the chart inclusion. -/
noncomputable def schemeModuleProjectiveSectionChartAmbientι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionChartAmbient base M j ⟶
      pullback base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M) :=
  let V := SchemeModuleGlobalSectionsOver base M
  pullback.map base (finiteDimensionalProjectiveChartToBase K V j)
    base (finiteDimensionalProjectiveParametersToBase K V)
    (𝟙 X) (finiteDimensionalProjectiveChartι K V j) (𝟙 (Spec (.of K)))
    (by simp)
    (by
      rw [Category.comp_id, finiteDimensionalProjectiveChartι_toBase])

instance schemeModuleProjectiveSectionChartAmbientι_isOpenImmersion
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    IsOpenImmersion
      (schemeModuleProjectiveSectionChartAmbientι base M j) := by
  unfold schemeModuleProjectiveSectionChartAmbientι
  apply Scheme.pullback_map_isOpenImmersion

/-- The chart-ambient inclusion is the identity on the surface factor. -/
theorem schemeModuleProjectiveSectionChartAmbientι_fst
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionChartAmbientι base M j ≫
        pullback.fst base
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M) =
      pullback.fst base
        (finiteDimensionalProjectiveChartToBase K
          (SchemeModuleGlobalSectionsOver base M) j) := by
  unfold schemeModuleGlobalSectionsProjectiveParametersToBase
  simp only [schemeModuleProjectiveSectionChartAmbientι, pullback.map,
    pullback.lift_fst, Category.comp_id]

/-- The chart-ambient inclusion uses the standard projective chart on the
parameter factor. -/
theorem schemeModuleProjectiveSectionChartAmbientι_snd
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionChartAmbientι base M j ≫
        pullback.snd base
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M) =
      pullback.snd base
          (finiteDimensionalProjectiveChartToBase K
            (SchemeModuleGlobalSectionsOver base M) j) ≫
        finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) j := by
  unfold schemeModuleGlobalSectionsProjectiveParametersToBase
  simp only [schemeModuleProjectiveSectionChartAmbientι, pullback.map,
    pullback.lift_snd]

/-- The normalized `i`th projective coefficient, regarded as a regular
function on the surface–parameter-chart fibre product. -/
noncomputable def schemeModuleProjectiveSectionChartCoefficient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    Γ(schemeModuleProjectiveSectionChartAmbient base M j, ⊤) :=
  let V := SchemeModuleGlobalSectionsOver base M
  let R := finiteDimensionalProjectiveChartRing K V j
  (pullback.snd base (finiteDimensionalProjectiveChartToBase K V j)).appTop.hom
    ((Scheme.ΓSpecIso (.of R)).inv.hom
      (chartCoordinate (finiteDimensionalProjectiveIdeal K V) j i))

/-- The distinguished coefficient on its own normalized chart is one. -/
theorem schemeModuleProjectiveSectionChartCoefficient_self
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionChartCoefficient base M j j = 1 := by
  unfold schemeModuleProjectiveSectionChartCoefficient
  dsimp only
  rw [chartCoordinate_self, map_one, map_one]

/-- The normalized universal section on one standard chart of the
projectivized global-section space. -/
noncomputable def schemeModuleProjectiveSectionChartUniversalSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    ((Scheme.Modules.pullback
      (pullback.fst base
        (finiteDimensionalProjectiveChartToBase K
          (SchemeModuleGlobalSectionsOver base M) j))).obj M).sections :=
  parameterizedSchemeModuleSection
    (ι := Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    base M
    (pullback.fst base
      (finiteDimensionalProjectiveChartToBase K
        (SchemeModuleGlobalSectionsOver base M) j))
    (schemeModuleProjectiveSectionChartCoefficient base M j)
    (fun i => Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i)

end

end PfaffianDescent
