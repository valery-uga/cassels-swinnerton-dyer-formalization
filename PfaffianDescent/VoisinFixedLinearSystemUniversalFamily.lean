import PfaffianDescent.VoisinFixedLinearSystemUniversalOverlap
import AllCharacteristics.SectionResidueField
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# The global ambient cover for a projective system of module sections

The normalized universal sections have been constructed on the standard
projective parameter charts and compared on their overlaps.  This file starts
the global zero-family construction by exhibiting those parameter charts as
an actual open cover after base change to the surface.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective

universe u v

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Evaluate a global regular function along a field-valued scheme point,
using the canonical identification of the residue field of `Spec L` with
`L`. -/
noncomputable def fieldPointΓevaluation
    {L : Type u} [Field L] {X : Scheme.{u}}
  (f : Spec (.of L) ⟶ X) : Γ(X, ⊤) →+* L :=
  (AllCharacteristics.specFieldClosedPointResidueIso L).toRingHom.comp
    ((f.residueFieldMap
      (IsLocalRing.closedPoint L : Spec (.of L))).hom.comp
      (X.Γevaluation
        (f (IsLocalRing.closedPoint L : Spec (.of L)))).hom)

/-- A function vanishing in the residue field at the image of a field-valued
point also vanishes after evaluation in that point's coefficient field. -/
theorem fieldPointΓevaluation_eq_zero_of_Γevaluation_eq_zero
    {L : Type u} [Field L] {X : Scheme.{u}}
    (f : Spec (.of L) ⟶ X) (a : Γ(X, ⊤))
    (ha : X.Γevaluation
      (f (IsLocalRing.closedPoint L : Spec (.of L))) a = 0) :
    fieldPointΓevaluation f a = 0 := by
  unfold fieldPointΓevaluation
  rw [RingHom.comp_apply, RingHom.comp_apply, ha, map_zero, map_zero]

/-- Evaluation in the coefficient field of a field-valued point detects
vanishing in the residue field at its image.  The residue-field maps are
injective because their sources are fields. -/
theorem Γevaluation_eq_zero_of_fieldPointΓevaluation_eq_zero
    {L : Type u} [Field L] {X : Scheme.{u}}
    (f : Spec (.of L) ⟶ X) (a : Γ(X, ⊤))
    (ha : fieldPointΓevaluation f a = 0) :
    X.Γevaluation
      (f (IsLocalRing.closedPoint L : Spec (.of L))) a = 0 := by
  let r : X.residueField
        (f (IsLocalRing.closedPoint L : Spec (.of L))) →+* L :=
    (AllCharacteristics.specFieldClosedPointResidueIso L).toRingHom.comp
      (f.residueFieldMap
        (IsLocalRing.closedPoint L : Spec (.of L))).hom
  unfold fieldPointΓevaluation at ha
  apply r.injective
  change r (X.Γevaluation
    (f (IsLocalRing.closedPoint L : Spec (.of L))) a) = r 0
  simpa only [r, RingHom.comp_apply, map_zero] using ha

/-- Field-point evaluation is functorial under composition with a scheme
morphism. -/
theorem fieldPointΓevaluation_comp
    {L : Type u} [Field L] {X Y : Scheme.{u}}
    (f : Spec (.of L) ⟶ X) (g : X ⟶ Y) (a : Γ(Y, ⊤)) :
    fieldPointΓevaluation (f ≫ g) a =
      fieldPointΓevaluation f (g.appTop a) := by
  let s : Spec (.of L) := IsLocalRing.closedPoint L
  unfold fieldPointΓevaluation
  simp only [RingHom.comp_apply]
  change
    (AllCharacteristics.specFieldClosedPointResidueIso L)
        ((f ≫ g).residueFieldMap s (Y.Γevaluation ((f ≫ g) s) a)) =
      (AllCharacteristics.specFieldClosedPointResidueIso L)
        (f.residueFieldMap s (X.Γevaluation (f s) (g.appTop a)))
  rw [Scheme.residueFieldMap_comp]
  change
    (AllCharacteristics.specFieldClosedPointResidueIso L)
        (f.residueFieldMap s
          (g.residueFieldMap (f s) (Y.Γevaluation (g (f s)) a))) = _
  rw [Scheme.Γevaluation_naturality_apply g (f s) a]

/-- On the spectrum of a field, evaluation at its unique point is the
canonical global-sections isomorphism. -/
theorem fieldPointΓevaluation_id
    {L : Type u} [Field L] (a : Γ(Spec (.of L), ⊤)) :
    fieldPointΓevaluation (𝟙 (Spec (.of L))) a =
      (Scheme.ΓSpecIso (.of L)).hom.hom a := by
  let x := (Scheme.ΓSpecIso (.of L)).hom.hom a
  have ha : (Scheme.ΓSpecIso (.of L)).inv.hom x = a := by
    dsimp only [x]
    exact (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso (.of L)).hom_inv_id) a
  rw [← ha]
  unfold fieldPointΓevaluation
  let s : Spec (.of L) := IsLocalRing.closedPoint L
  change
    (AllCharacteristics.specFieldClosedPointResidueIso L)
        (Scheme.Hom.residueFieldMap (𝟙 (Spec (.of L))) s
          ((Spec (.of L)).Γevaluation ((𝟙 (Spec (.of L))) s)
            ((Scheme.ΓSpecIso (.of L)).inv.hom x))) =
      (Scheme.ΓSpecIso (.of L)).hom.hom
        ((Scheme.ΓSpecIso (.of L)).inv.hom x)
  rw [Scheme.residueFieldMap_id]
  simp
  change
    (AllCharacteristics.specFieldClosedPointResidueIso L)
        ((Spec (.of L)).Γevaluation s
          ((Scheme.ΓSpecIso (.of L)).inv.hom x)) = x
  unfold Scheme.Γevaluation Scheme.evaluation
  have h := Scheme.Spec.algebraMap_residueFieldIso_inv (.of L) s
  change
    (AllCharacteristics.specFieldClosedPointResidueIso L).toRingHom.comp
        (((Scheme.ΓSpecIso (.of L)).inv ≫
          (Spec (.of L)).presheaf.germ ⊤ s trivial ≫
          (Spec (.of L)).residue s).hom) x = x
  rw [← h]
  dsimp only [s]
  unfold AllCharacteristics.specFieldClosedPointResidueIso
  simp only [RingHom.comp_apply]
  change
    (Ideal.algEquivResidueFieldOfField
        (IsLocalRing.closedPoint L).asIdeal).symm
      ((Scheme.Spec.residueFieldIso (.of L)
        (IsLocalRing.closedPoint L)).commRingCatIsoToRingEquiv
          ((Scheme.Spec.residueFieldIso (.of L)
            (IsLocalRing.closedPoint L)).inv.hom
              (algebraMap L
                (IsLocalRing.closedPoint L).asIdeal.ResidueField x))) = x
  rw [show
    (Scheme.Spec.residueFieldIso (.of L)
        (IsLocalRing.closedPoint L)).commRingCatIsoToRingEquiv
      ((Scheme.Spec.residueFieldIso (.of L)
        (IsLocalRing.closedPoint L)).inv.hom
          (algebraMap L
            (IsLocalRing.closedPoint L).asIdeal.ResidueField x)) =
      algebraMap L (IsLocalRing.closedPoint L).asIdeal.ResidueField x by
        exact
          (Scheme.Spec.residueFieldIso (.of L)
            (IsLocalRing.closedPoint L)).commRingCatIsoToRingEquiv.apply_symm_apply _]
  rw [← Ideal.algEquivResidueFieldOfField_apply]
  exact Equiv.symm_apply_apply _ x

/-- Evaluation at a field-valued point is the value of the pulled-back
global function on the spectrum of its coefficient field.  This form is
useful when comparing local section coordinates after field base change. -/
theorem fieldPointΓevaluation_eq_appTop
    {L : Type u} [Field L] {X : Scheme.{u}}
    (f : Spec (.of L) ⟶ X) (a : Γ(X, ⊤)) :
    fieldPointΓevaluation f a =
      (Scheme.ΓSpecIso (.of L)).hom.hom (f.appTop a) := by
  have h := fieldPointΓevaluation_comp
    (𝟙 (Spec (.of L))) f a
  rw [Category.id_comp, fieldPointΓevaluation_id] at h
  exact h

/-- Evaluating an affine coordinate along `Spec.map b` gives its image under
the ring homomorphism `b`. -/
theorem fieldPointΓevaluation_Spec_map
    {R L : Type u} [CommRing R] [Field L]
    (b : R →+* L) (x : R) :
    fieldPointΓevaluation (Spec.map (CommRingCat.ofHom b))
        ((Scheme.ΓSpecIso (.of R)).inv.hom x) = b x := by
  have h := fieldPointΓevaluation_comp (𝟙 (Spec (.of L)))
    (Spec.map (CommRingCat.ofHom b))
    ((Scheme.ΓSpecIso (.of R)).inv.hom x)
  rw [Category.id_comp] at h
  rw [h, fieldPointΓevaluation_id]
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom b))
    ((Scheme.ΓSpecIso (.of R)).inv.hom x)
  simp only [ConcreteCategory.comp_apply] at hn
  have hx : (Scheme.ΓSpecIso (.of R)).hom.hom
      ((Scheme.ΓSpecIso (.of R)).inv.hom x) = x := by
    exact ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso (.of R)).inv_hom_id x
  rw [hx] at hn
  exact hn

/-- Evaluation of a global function commutes with extending the coefficient
field of a scheme-valued point. -/
theorem fieldPointΓevaluation_fieldExtension
    {L M : Type u} [Field L] [Field M] {X : Scheme.{u}}
    (b : L →+* M) (f : Spec (.of L) ⟶ X) (a : Γ(X, ⊤)) :
    fieldPointΓevaluation
        (Spec.map (CommRingCat.ofHom b) ≫ f) a =
      b (fieldPointΓevaluation f a) := by
  rw [fieldPointΓevaluation_comp]
  have hx : (Scheme.ΓSpecIso (.of L)).inv.hom
      (fieldPointΓevaluation f a) = f.appTop a := by
    rw [fieldPointΓevaluation_eq_appTop]
    exact ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso (.of L)).hom_inv_id (f.appTop a)
  rw [← hx, fieldPointΓevaluation_Spec_map]

set_option backward.isDefEq.respectTransparency false in
/-- Pulling a finite parameterized section to an affine open and transporting
through pullback composition gives the parameterized section with every
coefficient restricted along that open. -/
theorem parameterizedSchemeModuleSection_pullback
    {K : Type u} [Field K] {X U W : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι : Type v} [Fintype ι]
    (p : U ⟶ X) (q : W ⟶ U) [IsOpenImmersion q]
    (coeff : ι → Γ(U, ⊤))
    (s : ι → SchemeModuleGlobalSectionsOver base M) :
    SheafOfModules.sectionsMap
      ((Scheme.Modules.pullbackComp q p).app M).hom
      (BundleSectionZeroLocus.pullbackSection q
        ((Scheme.Modules.pullback p).obj M)
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison q)
        (parameterizedSchemeModuleSection base M p coeff s)) =
      parameterizedSchemeModuleSection base M (q ≫ p)
        (fun i => q.appTop (coeff i)) s := by
  unfold parameterizedSchemeModuleSection finiteLinearCombinationSections
  rw [pullbackSection_sumSections, sectionsMap_sumSections]
  congr 1
  funext i
  rw [BundleSectionZeroLocus.pullbackSection_scaleSection,
    BundleSectionZeroLocus.sectionsMap_scaleSection,
    BundleSectionZeroLocus.pullbackUnitEndomorphismOfRegularFunction_eq_appTop]
  exact congrArg
    (BundleSectionZeroLocus.scaleSection
      (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
        (q.appTop (coeff i))))
    (BundleSectionZeroLocus.sectionsMap_pullbackComp_pullbackCongr_pullbackSection
      q p (q ≫ p) rfl M
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison q)
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison p)
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison (q ≫ p))
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison (q ≫ p))
      (schemeModuleGlobalSectionsOverEquivSections base M (s i)))

set_option backward.isDefEq.respectTransparency false in
/-- Transporting a parameterized section along equality of its map to the
original scheme changes only the pullback-module presentation. -/
theorem parameterizedSchemeModuleSection_pullbackCongr
    {K : Type u} [Field K] {X W : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι : Type v} [Fintype ι]
    (p q : W ⟶ X) (h : p = q)
    (coeff : ι → Γ(W, ⊤))
    (s : ι → SchemeModuleGlobalSectionsOver base M) :
    SheafOfModules.sectionsMap
      ((Scheme.Modules.pullbackCongr h).app M).hom
      (parameterizedSchemeModuleSection base M p coeff s) =
      parameterizedSchemeModuleSection base M q coeff s := by
  unfold parameterizedSchemeModuleSection finiteLinearCombinationSections
  rw [sectionsMap_sumSections]
  congr 1
  funext i
  rw [BundleSectionZeroLocus.sectionsMap_scaleSection]
  exact congrArg
    (BundleSectionZeroLocus.scaleSection
      (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction (coeff i)))
    (BundleSectionZeroLocus.sectionsMap_pullbackCongr_pullbackSection
      p q h M
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison p)
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison q)
      (schemeModuleGlobalSectionsOverEquivSections base M (s i)))

/-- The standard normalized parameter charts, regarded as an affine open
cover of the projective space of global sections. -/
noncomputable def schemeModuleGlobalSectionsProjectiveParameterChartCover
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)] :
    (schemeModuleGlobalSectionsProjectiveParameters base M).AffineOpenCover :=
  coordinateOpenCover (finiteDimensionalProjectiveIdeal K
    (SchemeModuleGlobalSectionsOver base M))

/-- Base change of the normalized parameter-chart cover to the complete
surface--parameter ambient space.  This is the cover on which the local
universal zero schemes will be glued. -/
noncomputable def schemeModuleProjectiveSectionAmbientOpenCover
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)] :
    (pullback base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).OpenCover :=
  (schemeModuleGlobalSectionsProjectiveParameterChartCover base M).openCover.pullback₁
    (pullback.snd base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M))

/-- A chart of the pulled-back ambient cover maps to the corresponding
normalized parameter chart. -/
noncomputable def schemeModuleProjectiveSectionAmbientOpenCoverToParameterChart
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : (schemeModuleProjectiveSectionAmbientOpenCover base M).I₀) :
    (schemeModuleProjectiveSectionAmbientOpenCover base M).X j ⟶
      finiteDimensionalProjectiveChart K
        (SchemeModuleGlobalSectionsOver base M) j :=
  (schemeModuleGlobalSectionsProjectiveParameterChartCover base M).openCover.pullbackHom
    (pullback.snd base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)) j

/-- The preceding map followed by the standard chart inclusion is the
parameter projection of the pulled-back cover chart. -/
theorem schemeModuleProjectiveSectionAmbientOpenCoverToParameterChart_comp
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : (schemeModuleProjectiveSectionAmbientOpenCover base M).I₀) :
    schemeModuleProjectiveSectionAmbientOpenCoverToParameterChart base M j ≫
        finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) j =
      (schemeModuleProjectiveSectionAmbientOpenCover base M).f j ≫
        pullback.snd base
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M) := by
  exact Scheme.Cover.pullbackHom_map
    (schemeModuleGlobalSectionsProjectiveParameterChartCover base M).openCover
    (pullback.snd base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)) j

/-- Each member of the pulled-back cover is Cartesian over the corresponding
normalized parameter chart.  Thus it represents the same surface--chart
fibre product used to define the normalized universal section. -/
theorem isPullback_schemeModuleProjectiveSectionAmbientOpenCoverChart
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : (schemeModuleProjectiveSectionAmbientOpenCover base M).I₀) :
    IsPullback
      (schemeModuleProjectiveSectionAmbientOpenCoverToParameterChart base M j)
      ((schemeModuleProjectiveSectionAmbientOpenCover base M).f j ≫
        pullback.fst base
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M))
      (finiteDimensionalProjectiveChartToBase K
        (SchemeModuleGlobalSectionsOver base M) j)
      base := by
  let C := (schemeModuleGlobalSectionsProjectiveParameterChartCover base M).openCover
  let p := pullback.snd base
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
  have htop : IsPullback
      (schemeModuleProjectiveSectionAmbientOpenCoverToParameterChart base M j)
      ((schemeModuleProjectiveSectionAmbientOpenCover base M).f j)
      (finiteDimensionalProjectiveChartι K
        (SchemeModuleGlobalSectionsOver base M) j)
      p := by
    exact (IsPullback.of_hasPullback p
      (finiteDimensionalProjectiveChartι K
        (SchemeModuleGlobalSectionsOver base M) j)).flip
  have hbottom : IsPullback p
      (pullback.fst base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M))
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
      base :=
    (IsPullback.of_hasPullback base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).flip
  have h := htop.paste_vert hbottom
  have hbase := finiteDimensionalProjectiveChartι_toBase K
    (SchemeModuleGlobalSectionsOver base M) j
  change finiteDimensionalProjectiveChartι K
      (SchemeModuleGlobalSectionsOver base M) j ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M =
    finiteDimensionalProjectiveChartToBase K
      (SchemeModuleGlobalSectionsOver base M) j at hbase
  rw [hbase] at h
  exact h

/-- Canonical identification of a base-changed cover member with the
previously defined normalized chart ambient. -/
noncomputable def schemeModuleProjectiveSectionAmbientOpenCoverChartIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : (schemeModuleProjectiveSectionAmbientOpenCover base M).I₀) :
    (schemeModuleProjectiveSectionAmbientOpenCover base M).X j ≅
      schemeModuleProjectiveSectionChartAmbient base M j :=
  (isPullback_schemeModuleProjectiveSectionAmbientOpenCoverChart base M j).isoIsPullback
    (finiteDimensionalProjectiveChart K
      (SchemeModuleGlobalSectionsOver base M) j)
    X
    ((IsPullback.of_hasPullback base
      (finiteDimensionalProjectiveChartToBase K
        (SchemeModuleGlobalSectionsOver base M) j)).flip)

/-- The canonical chart identification preserves the parameter-chart
projection. -/
theorem schemeModuleProjectiveSectionAmbientOpenCoverChartIso_hom_snd
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : (schemeModuleProjectiveSectionAmbientOpenCover base M).I₀) :
    (schemeModuleProjectiveSectionAmbientOpenCoverChartIso base M j).hom ≫
        pullback.snd base
          (finiteDimensionalProjectiveChartToBase K
            (SchemeModuleGlobalSectionsOver base M) j) =
      schemeModuleProjectiveSectionAmbientOpenCoverToParameterChart base M j :=
  (isPullback_schemeModuleProjectiveSectionAmbientOpenCoverChart base M j).isoIsPullback_hom_fst
    (finiteDimensionalProjectiveChart K
      (SchemeModuleGlobalSectionsOver base M) j)
    X
    ((IsPullback.of_hasPullback base
      (finiteDimensionalProjectiveChartToBase K
        (SchemeModuleGlobalSectionsOver base M) j)).flip)

/-- The canonical chart identification preserves the surface projection. -/
theorem schemeModuleProjectiveSectionAmbientOpenCoverChartIso_hom_fst
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : (schemeModuleProjectiveSectionAmbientOpenCover base M).I₀) :
    (schemeModuleProjectiveSectionAmbientOpenCoverChartIso base M j).hom ≫
        pullback.fst base
          (finiteDimensionalProjectiveChartToBase K
            (SchemeModuleGlobalSectionsOver base M) j) =
      (schemeModuleProjectiveSectionAmbientOpenCover base M).f j ≫
        pullback.fst base
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M) :=
  (isPullback_schemeModuleProjectiveSectionAmbientOpenCoverChart base M j).isoIsPullback_hom_snd
    (finiteDimensionalProjectiveChart K
      (SchemeModuleGlobalSectionsOver base M) j)
    X
    ((IsPullback.of_hasPullback base
      (finiteDimensionalProjectiveChartToBase K
        (SchemeModuleGlobalSectionsOver base M) j)).flip)

set_option backward.isDefEq.respectTransparency false in
/-- Under the canonical identification, the normalized chart's previously
defined inclusion into the complete ambient product is exactly the map of the
base-changed open cover. -/
theorem schemeModuleProjectiveSectionAmbientOpenCoverChartIso_hom_comp_ambientι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : (schemeModuleProjectiveSectionAmbientOpenCover base M).I₀) :
    (schemeModuleProjectiveSectionAmbientOpenCoverChartIso base M j).hom ≫
        schemeModuleProjectiveSectionChartAmbientι base M j =
      (schemeModuleProjectiveSectionAmbientOpenCover base M).f j := by
  apply pullback.hom_ext
  · simp only [Category.assoc,
      schemeModuleProjectiveSectionChartAmbientι_fst,
      schemeModuleProjectiveSectionAmbientOpenCoverChartIso_hom_fst]
  · rw [Category.assoc,
      schemeModuleProjectiveSectionChartAmbientι_snd,
      ← Category.assoc,
      schemeModuleProjectiveSectionAmbientOpenCoverChartIso_hom_snd,
      schemeModuleProjectiveSectionAmbientOpenCoverToParameterChart_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The normalized chart ambients therefore form an open cover of the full
surface--projective-section ambient space, up to their canonical Cartesian
identifications. -/
theorem schemeModuleProjectiveSectionChartAmbientι_jointly_surjective
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (x : (CategoryTheory.Limits.pullback base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M) : Scheme.{u})) :
    ∃ (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
      (y : schemeModuleProjectiveSectionChartAmbient base M j),
      schemeModuleProjectiveSectionChartAmbientι base M j y = x := by
  obtain ⟨j, z, hz⟩ :=
    (schemeModuleProjectiveSectionAmbientOpenCover base M).exists_eq x
  change Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)) at j
  refine ⟨j, (schemeModuleProjectiveSectionAmbientOpenCoverChartIso base M j).hom z, ?_⟩
  have hmap := congrArg
    (fun q : (schemeModuleProjectiveSectionAmbientOpenCover base M).X j ⟶
        pullback base
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M) => q z)
    (schemeModuleProjectiveSectionAmbientOpenCoverChartIso_hom_comp_ambientι
      base M j)
  exact hmap.trans hz

/-- An affine cover on which a scheme module has one fixed finite free
presentation.  This is the local input needed to turn the universal section
into coordinate ideals without assuming that the bundle is globally free. -/
structure SchemeModuleFiniteFreeAffineCover
    {X : Scheme.{u}} (M : X.Modules) (I : Type u) where
  ι : Type u
  U : ι → X.Opens
  covers : ⨆ i, U i = ⊤
  affine : ∀ i, IsAffine (U i : Scheme.{u})
  trivialization : ∀ i,
    SheafOfModules.free (R := X.ringCatSheaf.over (U i)) I ≅ M.over (U i)

namespace SchemeModuleFiniteFreeAffineCover

/-- A field-valued point of the base scheme factors through one member of a
finite-free affine trivializing cover. -/
theorem exists_fieldPoint_lift
    {L : Type u} [Field L] {X : Scheme.{u}} {M : X.Modules} {I : Type u}
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (a : Spec (.of L) ⟶ X) :
    ∃ (i : C.ι) (aU : Spec (.of L) ⟶ (C.U i : Scheme.{u})),
      aU ≫ (C.U i).ι = a := by
  let s : Spec (.of L) := IsLocalRing.closedPoint L
  have hs : a s ∈ ⨆ i, C.U i := by rw [C.covers]; trivial
  rw [TopologicalSpace.Opens.mem_iSup] at hs
  obtain ⟨i, hi⟩ := hs
  have hrange : Set.range a ⊆ Set.range (C.U i).ι := by
    rintro x ⟨t, rfl⟩
    have ht : t = s := Subsingleton.elim _ _
    subst t
    exact ⟨⟨a s, hi⟩, rfl⟩
  let aU := IsOpenImmersion.lift (C.U i).ι a hrange
  exact ⟨i, aU, IsOpenImmersion.lift_fac _ _ _⟩

/-- The displayed trivializing opens form an actual scheme-theoretic open
cover of the original scheme. -/
noncomputable def openCover
    {X : Scheme.{u}} {M : X.Modules} {I : Type u}
    (C : SchemeModuleFiniteFreeAffineCover M I) : X.OpenCover where
  I₀ := C.ι
  X i := C.U i
  f i := (C.U i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ ↦ inferInstance⟩
    intro x
    have hx : x ∈ ⨆ i, C.U i := by rw [C.covers]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨i, hxi⟩ := hx
    exact ⟨i, ⟨x, hxi⟩, rfl⟩

/-- Product of a module-trivializing affine cover with the normalized affine
cover of its projective section parameters.  Its charts are precisely the
affine spaces on which coordinate zero ideals for the universal section are
defined. -/
noncomputable def projectiveSectionOpenCover
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I) :
    (pullback base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight C.openCover
    (schemeModuleGlobalSectionsProjectiveParameterChartCover base M).openCover
    base (schemeModuleGlobalSectionsProjectiveParametersToBase base M)

/-- Every trivialized surface--parameter product chart is affine. -/
instance projectiveSectionOpenCover_affine
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    IsAffine ((C.projectiveSectionOpenCover base M).X ij) := by
  change IsAffine (pullback ((C.U ij.1).ι ≫ base)
    ((finiteDimensionalProjectiveChartι K
        (SchemeModuleGlobalSectionsOver base M) ij.2) ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M))
  letI : IsAffine (C.U ij.1 : Scheme.{u}) := C.affine ij.1
  letI : IsAffine (finiteDimensionalProjectiveChart K
      (SchemeModuleGlobalSectionsOver base M) ij.2) := by
    change IsAffine (Spec _)
    infer_instance
  infer_instance

/-- Projection of a trivialized product chart to its selected affine open on
the surface. -/
noncomputable abbrev projectiveSectionOpenCoverToSurfaceChart
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionOpenCover base M).X ij ⟶ (C.U ij.1 : Scheme.{u}) :=
  pullback.fst ((C.U ij.1).ι ≫ base)
    ((finiteDimensionalProjectiveChartι K
      (SchemeModuleGlobalSectionsOver base M) ij.2) ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M)

/-- Projection of a trivialized product chart to its normalized affine
parameter chart. -/
noncomputable abbrev projectiveSectionOpenCoverToParameterChart
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionOpenCover base M).X ij ⟶
      finiteDimensionalProjectiveChart K
        (SchemeModuleGlobalSectionsOver base M) ij.2 :=
  pullback.snd ((C.U ij.1).ι ≫ base)
    ((finiteDimensionalProjectiveChartι K
      (SchemeModuleGlobalSectionsOver base M) ij.2) ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M)

/-- Map from a trivialized product chart to the original surface. -/
noncomputable abbrev projectiveSectionOpenCoverToSurface
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionOpenCover base M).X ij ⟶ X :=
  C.projectiveSectionOpenCoverToSurfaceChart base M ij ≫ (C.U ij.1).ι

/-- A field-valued surface point and a field-valued normalized parameter
point over the same base lift together to one product chart of the universal
section cover.  The surface chart may depend on the point, while the chosen
projective chart is retained. -/
theorem exists_projectiveSectionOpenCover_fieldPoint_lift
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    (a : Spec (.of L) ⟶ X)
    (t : Spec (.of L) ⟶ finiteDimensionalProjectiveChart K
      (SchemeModuleGlobalSectionsOver base M) j)
    (hat : a ≫ base = t ≫ finiteDimensionalProjectiveChartToBase K
      (SchemeModuleGlobalSectionsOver base M) j) :
    ∃ (ij : C.openCover.I₀ ×
        (schemeModuleGlobalSectionsProjectiveParameterChartCover base M).openCover.I₀)
      (r : Spec (.of L) ⟶ (C.projectiveSectionOpenCover base M).X ij),
      ij.2 = j ∧
      r ≫ C.projectiveSectionOpenCoverToSurface base M ij = a ∧
      r ≫ C.projectiveSectionOpenCoverToParameterChart base M ij ≫
          finiteDimensionalProjectiveChartι K
            (SchemeModuleGlobalSectionsOver base M) ij.2 =
        t ≫ finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) j := by
  obtain ⟨i, aU, haU⟩ := C.exists_fieldPoint_lift a
  change C.openCover.I₀ at i
  change (schemeModuleGlobalSectionsProjectiveParameterChartCover base M).openCover.I₀ at j
  let ij := (i, j)
  have hbase : aU ≫ (C.U i).ι ≫ base =
      t ≫ finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) j ≫
        finiteDimensionalProjectiveParametersToBase K
          (SchemeModuleGlobalSectionsOver base M) := by
    calc
      _ = a ≫ base := by rw [← Category.assoc, haU]
      _ = _ := hat
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun f => t ≫ f)
          (finiteDimensionalProjectiveChartι_toBase K
            (SchemeModuleGlobalSectionsOver base M) j).symm
  let r : Spec (.of L) ⟶ (C.projectiveSectionOpenCover base M).X ij :=
    pullback.lift aU t hbase
  refine ⟨ij, r, rfl, ?_, ?_⟩
  · dsimp only [r, ij]
    change (pullback.lift aU t hbase ≫
        pullback.fst ((C.U i).ι ≫ base)
          (finiteDimensionalProjectiveChartι K
            (SchemeModuleGlobalSectionsOver base M) j ≫
              finiteDimensionalProjectiveParametersToBase K
                (SchemeModuleGlobalSectionsOver base M))) ≫ (C.U i).ι = a
    rw [pullback.lift_fst, haU]
  · dsimp only [r, ij]
    change (pullback.lift aU t hbase ≫
        pullback.snd ((C.U i).ι ≫ base)
          (finiteDimensionalProjectiveChartι K
            (SchemeModuleGlobalSectionsOver base M) j ≫
              finiteDimensionalProjectiveParametersToBase K
                (SchemeModuleGlobalSectionsOver base M))) ≫
        finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) j =
      t ≫ finiteDimensionalProjectiveChartι K
        (SchemeModuleGlobalSectionsOver base M) j
    rw [pullback.lift_snd]

/-- Equality of the reconstructed projective point on a fixed normalized
chart forces equality of the underlying chart-ring homomorphisms.  Thus the
coefficient functions evaluated through a product chart are literally the
common coefficients of the chosen projective parameter. -/
theorem projectiveSectionOpenCoverToParameterChart_preimage_eq
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (r : Spec (.of L) ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (b : finiteDimensionalProjectiveChartRing K
      (SchemeModuleGlobalSectionsOver base M) ij.2 →+* L)
    (hparameter : r ≫ C.projectiveSectionOpenCoverToParameterChart base M ij ≫
        finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) ij.2 =
      Spec.map (CommRingCat.ofHom b) ≫
        finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) ij.2) :
    (Spec.preimage
      (r ≫ C.projectiveSectionOpenCoverToParameterChart base M ij)).hom = b := by
  change C.openCover.I₀ ×
    (schemeModuleGlobalSectionsProjectiveParameterChartCover base M).openCover.I₀ at ij
  apply chart_hom_eq_of_projective_eq
    (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver base M))
  change Spec.map (Spec.preimage
      (r ≫ C.projectiveSectionOpenCoverToParameterChart base M ij)) ≫
      finiteDimensionalProjectiveChartι K
        (SchemeModuleGlobalSectionsOver base M) ij.2 = _
  rw [Spec.map_preimage]
  exact hparameter

/-- A refined affine product chart maps to the normalized chart ambient with
the same projective coordinate. -/
noncomputable def projectiveSectionOpenCoverToChartAmbient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionOpenCover base M).X ij ⟶
      schemeModuleProjectiveSectionChartAmbient base M ij.2 :=
  pullback.lift
    (C.projectiveSectionOpenCoverToSurface base M ij)
    (C.projectiveSectionOpenCoverToParameterChart base M ij)
    (by
      change C.openCover.I₀ ×
        (schemeModuleGlobalSectionsProjectiveParameterChartCover base M).openCover.I₀ at ij
      change
        (pullback.fst ((C.U ij.1).ι ≫ base)
            (finiteDimensionalProjectiveChartι K
              (SchemeModuleGlobalSectionsOver base M) ij.2 ≫
                schemeModuleGlobalSectionsProjectiveParametersToBase base M) ≫
          (C.U ij.1).ι) ≫ base =
        pullback.snd ((C.U ij.1).ι ≫ base)
            (finiteDimensionalProjectiveChartι K
              (SchemeModuleGlobalSectionsOver base M) ij.2 ≫
                schemeModuleGlobalSectionsProjectiveParametersToBase base M) ≫
          finiteDimensionalProjectiveChartToBase K
            (SchemeModuleGlobalSectionsOver base M) ij.2
      have hbase := finiteDimensionalProjectiveChartι_toBase K
        (SchemeModuleGlobalSectionsOver base M) ij.2
      change finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) ij.2 ≫
          schemeModuleGlobalSectionsProjectiveParametersToBase base M =
        finiteDimensionalProjectiveChartToBase K
          (SchemeModuleGlobalSectionsOver base M) ij.2 at hbase
      rw [Category.assoc, hbase]
      exact pullback.condition)

/-- The refined-chart map recovers its surface projection. -/
@[reassoc]
theorem projectiveSectionOpenCoverToChartAmbient_fst
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverToChartAmbient base M ij ≫
        pullback.fst base
          (finiteDimensionalProjectiveChartToBase K
            (SchemeModuleGlobalSectionsOver base M) ij.2) =
      C.projectiveSectionOpenCoverToSurface base M ij :=
  pullback.lift_fst _ _ _

/-- The refined-chart map recovers its normalized parameter projection. -/
@[reassoc]
theorem projectiveSectionOpenCoverToChartAmbient_snd
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverToChartAmbient base M ij ≫
        pullback.snd base
          (finiteDimensionalProjectiveChartToBase K
            (SchemeModuleGlobalSectionsOver base M) ij.2) =
      C.projectiveSectionOpenCoverToParameterChart base M ij :=
  pullback.lift_snd _ _ _

/-- Pullback of the original module to a trivialized product chart. -/
noncomputable abbrev projectiveSectionLocalModule
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :=
  (Scheme.Modules.pullback
    (C.projectiveSectionOpenCoverToSurface base M ij)).obj M

/-- The chosen bundle trivialization remains a finite free presentation on
each surface--parameter product chart. -/
noncomputable def projectiveSectionLocalFreeIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    SheafOfModules.free
        (R := (C.projectiveSectionOpenCover base M).X ij |>.ringCatSheaf) I ≅
      C.projectiveSectionLocalModule base M ij := by
  let p := C.projectiveSectionOpenCoverToSurfaceChart base M ij
  let U := C.U ij.1
  exact
    BundleSectionZeroLocus.pullbackFreeIso p I
      (BundleSectionZeroLocus.localFreeIsoOfOver U I (C.trivialization ij.1)) ≪≫
    (Scheme.Modules.pullback p).mapIso
      ((Scheme.Modules.overFunctorEquiv U).app M ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M) ≪≫
    (Scheme.Modules.pullbackComp p U.ι).app M

/-- The normalized `i`th coefficient function on a trivialized product
chart whose parameter coordinate `j` has been set to one. -/
noncomputable def projectiveSectionLocalCoefficient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    Γ((C.projectiveSectionOpenCover base M).X ij, ⊤) :=
  let V := SchemeModuleGlobalSectionsOver base M
  let R := finiteDimensionalProjectiveChartRing K V ij.2
  (C.projectiveSectionOpenCoverToParameterChart base M ij).appTop.hom
    ((Scheme.ΓSpecIso (.of R)).inv.hom
      (chartCoordinate (finiteDimensionalProjectiveIdeal K V) ij.2 i))

/-- At a field-valued product-chart point, a normalized local coefficient
evaluates to the corresponding coordinate of the chart-ring point. -/
theorem projectiveSectionLocalCoefficient_fieldPoint_eq
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (r : Spec (.of L) ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (b : finiteDimensionalProjectiveChartRing K
      (SchemeModuleGlobalSectionsOver base M) ij.2 →+* L)
    (hb : (Spec.preimage
      (r ≫ C.projectiveSectionOpenCoverToParameterChart base M ij)).hom = b)
    (i : Fin (Module.finrank K
      (SchemeModuleGlobalSectionsOver base M))) :
    fieldPointΓevaluation r
        (C.projectiveSectionLocalCoefficient base M ij i) =
      b (chartCoordinate
        (finiteDimensionalProjectiveIdeal K
          (SchemeModuleGlobalSectionsOver base M)) ij.2 i) := by
  change C.openCover.I₀ ×
    (schemeModuleGlobalSectionsProjectiveParameterChartCover base M).openCover.I₀ at ij
  unfold projectiveSectionLocalCoefficient
  rw [← fieldPointΓevaluation_comp]
  have hb' : Spec.preimage
      (r ≫ C.projectiveSectionOpenCoverToParameterChart base M ij) =
      CommRingCat.ofHom b := by
    ext x
    exact DFunLike.congr_fun hb x
  have hm : r ≫ C.projectiveSectionOpenCoverToParameterChart base M ij =
      Spec.map (CommRingCat.ofHom b) := by
    rw [← Spec.map_preimage
      (r ≫ C.projectiveSectionOpenCoverToParameterChart base M ij), hb']
  rw [hm]
  exact fieldPointΓevaluation_Spec_map b _

/-- Evaluation of one chosen local free coordinate of a ground global
section at a field-valued product-chart point, extended linearly from the
chosen finite basis.  This is the ground linear functional whose scalar
extension is compared with geometric evaluation after base change. -/
noncomputable def projectiveSectionLocalBasisCoordinateEvaluationLinearMap
    {K L : Type u} [Field K] [Field L] [Algebra K L] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (r : Spec (.of L) ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (a : I) : SchemeModuleGlobalSectionsOver base M →ₗ[K] L :=
  (Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).constr K
    (fun k =>
      fieldPointΓevaluation r
        (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
          (C.projectiveSectionLocalFreeIso base M ij)
          (BundleSectionZeroLocus.pullbackSection
            (C.projectiveSectionOpenCoverToSurface base M ij) M
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison
              (C.projectiveSectionOpenCoverToSurface base M ij))
            (schemeModuleGlobalSectionsOverEquivSections base M
              (Module.finBasis K
                (SchemeModuleGlobalSectionsOver base M) k))) a))

@[simp]
theorem projectiveSectionLocalBasisCoordinateEvaluationLinearMap_finBasis
    {K L : Type u} [Field K] [Field L] [Algebra K L] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (r : Spec (.of L) ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (a : I)
    (k : Fin (Module.finrank K
      (SchemeModuleGlobalSectionsOver base M))) :
    C.projectiveSectionLocalBasisCoordinateEvaluationLinearMap
        base M ij r a
        (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k) =
      fieldPointΓevaluation r
        (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
          (C.projectiveSectionLocalFreeIso base M ij)
          (BundleSectionZeroLocus.pullbackSection
            (C.projectiveSectionOpenCoverToSurface base M ij) M
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison
              (C.projectiveSectionOpenCoverToSurface base M ij))
            (schemeModuleGlobalSectionsOverEquivSections base M
              (Module.finBasis K
                (SchemeModuleGlobalSectionsOver base M) k))) a) := by
  exact (Module.finBasis K
    (SchemeModuleGlobalSectionsOver base M)).constr_basis K _ k

/-- The distinguished normalized coefficient remains one after pullback to
each surface--parameter product chart. -/
theorem projectiveSectionLocalCoefficient_self
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalCoefficient base M ij ij.2 = 1 := by
  unfold projectiveSectionLocalCoefficient
  let V := SchemeModuleGlobalSectionsOver base M
  let j : Fin (Module.finrank K V) := ij.2
  change (C.projectiveSectionOpenCoverToParameterChart base M ij).appTop.hom
      ((Scheme.ΓSpecIso
        (.of (finiteDimensionalProjectiveChartRing K V j))).inv.hom
          (chartCoordinate (finiteDimensionalProjectiveIdeal K V) j j)) = 1
  rw [chartCoordinate_self, map_one, map_one]

/-- The universal projective section on one affine bundle-trivializing
surface--parameter chart. -/
noncomputable def projectiveSectionLocalUniversalSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionLocalModule base M ij).sections :=
  parameterizedSchemeModuleSection
    (ι := Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    base M (C.projectiveSectionOpenCoverToSurface base M ij)
    (C.projectiveSectionLocalCoefficient base M ij)
    (fun i => Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i)

/-- In a surface-chart trivialization, each scalar coordinate of the local
universal section is the normalized projective linear combination of the
corresponding coordinates of the pulled-back basis sections. -/
theorem projectiveSectionLocalUniversalSectionCoordinate_eq_sum
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) (a : I) :
    BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
        (C.projectiveSectionLocalFreeIso base M ij)
        (C.projectiveSectionLocalUniversalSection base M ij) a =
      ∑ i, C.projectiveSectionLocalCoefficient base M ij i *
        BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
          (C.projectiveSectionLocalFreeIso base M ij)
          (BundleSectionZeroLocus.pullbackSection
            (C.projectiveSectionOpenCoverToSurface base M ij) M
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison
              (C.projectiveSectionOpenCoverToSurface base M ij))
            (schemeModuleGlobalSectionsOverEquivSections base M
              (Module.finBasis K
                (SchemeModuleGlobalSectionsOver base M) i))) a := by
  unfold projectiveSectionLocalUniversalSection
  exact BundleSectionZeroLocus.sectionCoordinateOfFreeIso_parameterizedSchemeModuleSection
      base M _ _ _ I (C.projectiveSectionLocalFreeIso base M ij) a

/-- If the coefficients of a field-valued product-chart point are the
normalization of a vector `c`, then the weighted evaluation equations for
`c` force every coordinate of the local universal section to vanish.  This
is the forward bridge from a scalar-extended section to the local universal
zero family. -/
theorem projectiveSectionLocalUniversalSectionCoordinate_fieldPoint_eq_zero_of_weightedSum
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (r : Spec (.of L) ⟶ (C.projectiveSectionOpenCover base M).X ij)
    (b : finiteDimensionalProjectiveChartRing K
      (SchemeModuleGlobalSectionsOver base M) ij.2 →+* L)
    (hb : (Spec.preimage
      (r ≫ C.projectiveSectionOpenCoverToParameterChart base M ij)).hom = b)
    (c : Fin (Module.finrank K
      (SchemeModuleGlobalSectionsOver base M)) → L)
    (hcoordinate : ∀ i,
      b (chartCoordinate
        (finiteDimensionalProjectiveIdeal K
          (SchemeModuleGlobalSectionsOver base M)) ij.2 i) =
        (c ij.2)⁻¹ * c i)
    (hzero : ∀ a : I,
      ∑ i, c i *
        fieldPointΓevaluation r
          (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
            (C.projectiveSectionLocalFreeIso base M ij)
            (BundleSectionZeroLocus.pullbackSection
              (C.projectiveSectionOpenCoverToSurface base M ij) M
              (BundleSectionZeroLocus.isIso_pullbackUnitComparison
                (C.projectiveSectionOpenCoverToSurface base M ij))
              (schemeModuleGlobalSectionsOverEquivSections base M
                (Module.finBasis K
                  (SchemeModuleGlobalSectionsOver base M) i))) a) = 0) :
    ∀ a : I,
      fieldPointΓevaluation r
        (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
          (C.projectiveSectionLocalFreeIso base M ij)
          (C.projectiveSectionLocalUniversalSection base M ij) a) = 0 := by
  intro a
  rw [C.projectiveSectionLocalUniversalSectionCoordinate_eq_sum base M ij a]
  simp only [map_sum, map_mul]
  simp_rw [C.projectiveSectionLocalCoefficient_fieldPoint_eq
    base M ij r b hb, hcoordinate]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  simp only [hzero a, mul_zero]

/-- Coordinate ideal of the local universal section.  These ideals are the
affine pieces that will be identified on overlaps and glued. -/
noncomputable def projectiveSectionLocalZeroIdeal
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    Scheme.IdealSheafData ((C.projectiveSectionOpenCover base M).X ij) :=
  BundleSectionZeroLocus.sectionZeroIdealOfFreeIso I
    (C.projectiveSectionLocalFreeIso base M ij)
    (C.projectiveSectionLocalUniversalSection base M ij)

/-- The corresponding affine local zero scheme. -/
noncomputable abbrev projectiveSectionLocalZeroSubscheme
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) : Scheme.{u} :=
  (C.projectiveSectionLocalZeroIdeal base M ij).subscheme

/-- Canonical closed immersion of a local universal zero scheme into its
affine surface--parameter chart. -/
noncomputable def projectiveSectionLocalZeroSubschemeι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionLocalZeroSubscheme base M ij ⟶
      (C.projectiveSectionOpenCover base M).X ij :=
  (C.projectiveSectionLocalZeroIdeal base M ij).subschemeι

/-- Every scalar coordinate of the normalized universal section vanishes in
the residue field of a point of its local zero subscheme. -/
theorem projectiveSectionLocalUniversalSectionCoordinate_Γevaluation_eq_zero
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (y : C.projectiveSectionLocalZeroSubscheme base M ij) (a : I) :
    ((C.projectiveSectionOpenCover base M).X ij).Γevaluation
        (C.projectiveSectionLocalZeroSubschemeι base M ij y)
        (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
          (C.projectiveSectionLocalFreeIso base M ij)
          (C.projectiveSectionLocalUniversalSection base M ij) a) = 0 := by
  exact BundleSectionZeroLocus.idealSheafSubscheme_Γevaluation_eq_zero
    (C.projectiveSectionLocalZeroIdeal base M ij) y _
    (BundleSectionZeroLocus.sectionCoordinateOfFreeIso_mem_zeroIdeal I
      (C.projectiveSectionLocalFreeIso base M ij)
      (C.projectiveSectionLocalUniversalSection base M ij) a)

/-- At a point of a local universal zero subscheme, the evaluated normalized
coefficient vector annihilates every coordinate of the evaluated basis
sections. -/
theorem projectiveSectionLocalBasisCoordinate_linearCombination_eq_zero
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (y : C.projectiveSectionLocalZeroSubscheme base M ij) (a : I) :
    ∑ i,
        ((C.projectiveSectionOpenCover base M).X ij).Γevaluation
            (C.projectiveSectionLocalZeroSubschemeι base M ij y)
            (C.projectiveSectionLocalCoefficient base M ij i) *
          ((C.projectiveSectionOpenCover base M).X ij).Γevaluation
            (C.projectiveSectionLocalZeroSubschemeι base M ij y)
            (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
              (C.projectiveSectionLocalFreeIso base M ij)
              (BundleSectionZeroLocus.pullbackSection
                (C.projectiveSectionOpenCoverToSurface base M ij) M
                (BundleSectionZeroLocus.isIso_pullbackUnitComparison
                  (C.projectiveSectionOpenCoverToSurface base M ij))
                (schemeModuleGlobalSectionsOverEquivSections base M
                  (Module.finBasis K
                    (SchemeModuleGlobalSectionsOver base M) i))) a) = 0 := by
  have h := C.projectiveSectionLocalUniversalSectionCoordinate_Γevaluation_eq_zero
    base M ij y a
  rw [C.projectiveSectionLocalUniversalSectionCoordinate_eq_sum base M ij a] at h
  simpa only [map_sum, map_mul] using h

/-- Morphism-level form of the local kernel equation.  A field-valued point
of the local zero subscheme carries the entire normalized linear-combination
equation into its coefficient field. -/
theorem projectiveSectionLocalBasisCoordinate_fieldPoint_linearCombination_eq_zero
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (y : Spec (.of L) ⟶ C.projectiveSectionLocalZeroSubscheme base M ij)
    (a : I) :
    ∑ i,
        fieldPointΓevaluation
            (y ≫ C.projectiveSectionLocalZeroSubschemeι base M ij)
            (C.projectiveSectionLocalCoefficient base M ij i) *
          fieldPointΓevaluation
            (y ≫ C.projectiveSectionLocalZeroSubschemeι base M ij)
            (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
              (C.projectiveSectionLocalFreeIso base M ij)
              (BundleSectionZeroLocus.pullbackSection
                (C.projectiveSectionOpenCoverToSurface base M ij) M
                (BundleSectionZeroLocus.isIso_pullbackUnitComparison
                  (C.projectiveSectionOpenCoverToSurface base M ij))
                (schemeModuleGlobalSectionsOverEquivSections base M
                  (Module.finBasis K
                    (SchemeModuleGlobalSectionsOver base M) i))) a) = 0 := by
  let f := y ≫ C.projectiveSectionLocalZeroSubschemeι base M ij
  have h := C.projectiveSectionLocalBasisCoordinate_linearCombination_eq_zero
    base M ij (y (IsLocalRing.closedPoint L)) a
  have h' : ((C.projectiveSectionOpenCover base M).X ij).Γevaluation
      (f (IsLocalRing.closedPoint L))
      (∑ i, C.projectiveSectionLocalCoefficient base M ij i *
        BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
          (C.projectiveSectionLocalFreeIso base M ij)
          (BundleSectionZeroLocus.pullbackSection
            (C.projectiveSectionOpenCoverToSurface base M ij) M
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison
              (C.projectiveSectionOpenCoverToSurface base M ij))
          (schemeModuleGlobalSectionsOverEquivSections base M
              (Module.finBasis K
                (SchemeModuleGlobalSectionsOver base M) i))) a) = 0 := by
    have hf : f (IsLocalRing.closedPoint L) =
        C.projectiveSectionLocalZeroSubschemeι base M ij
          (y (IsLocalRing.closedPoint L)) := rfl
    rw [hf]
    simpa only [map_sum, map_mul] using h
  have hz := fieldPointΓevaluation_eq_zero_of_Γevaluation_eq_zero
    f
    (∑ i, C.projectiveSectionLocalCoefficient base M ij i *
      BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
        (C.projectiveSectionLocalFreeIso base M ij)
        (BundleSectionZeroLocus.pullbackSection
          (C.projectiveSectionOpenCoverToSurface base M ij) M
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison
            (C.projectiveSectionOpenCoverToSurface base M ij))
          (schemeModuleGlobalSectionsOverEquivSections base M
            (Module.finBasis K
              (SchemeModuleGlobalSectionsOver base M) i))) a) h'
  simpa only [map_sum, map_mul] using hz

/-- The evaluated normalized coefficient vector at a local zero-scheme point
is nonzero: its distinguished chart coordinate is one. -/
theorem projectiveSectionLocalEvaluatedCoefficient_ne_zero
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (y : C.projectiveSectionLocalZeroSubscheme base M ij) :
    (fun i =>
      ((C.projectiveSectionOpenCover base M).X ij).Γevaluation
        (C.projectiveSectionLocalZeroSubschemeι base M ij y)
        (C.projectiveSectionLocalCoefficient base M ij i)) ≠ 0 := by
  intro hzero
  have h := congrFun hzero ij.2
  rw [C.projectiveSectionLocalCoefficient_self base M ij, map_one] at h
  change (1 : ((C.projectiveSectionOpenCover base M).X ij).residueField
    (C.projectiveSectionLocalZeroSubschemeι base M ij y)) = 0 at h
  exact one_ne_zero h

/-- A point of a local universal zero subscheme supplies a nonzero normalized
coefficient vector over its residue field, and that vector annihilates every
free coordinate of the evaluated basis sections. -/
theorem exists_projectiveSectionLocalCoefficient_kernel
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀)
    (y : C.projectiveSectionLocalZeroSubscheme base M ij) :
    ∃ c : Fin (Module.finrank K
          (SchemeModuleGlobalSectionsOver base M)) →
        ((C.projectiveSectionOpenCover base M).X ij).residueField
          (C.projectiveSectionLocalZeroSubschemeι base M ij y),
      c ≠ 0 ∧ ∀ a : I,
        ∑ i, c i *
          ((C.projectiveSectionOpenCover base M).X ij).Γevaluation
            (C.projectiveSectionLocalZeroSubschemeι base M ij y)
            (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
              (C.projectiveSectionLocalFreeIso base M ij)
              (BundleSectionZeroLocus.pullbackSection
                (C.projectiveSectionOpenCoverToSurface base M ij) M
                (BundleSectionZeroLocus.isIso_pullbackUnitComparison
                  (C.projectiveSectionOpenCoverToSurface base M ij))
                (schemeModuleGlobalSectionsOverEquivSections base M
                  (Module.finBasis K
                    (SchemeModuleGlobalSectionsOver base M) i))) a) = 0 := by
  let c := fun i =>
    ((C.projectiveSectionOpenCover base M).X ij).Γevaluation
      (C.projectiveSectionLocalZeroSubschemeι base M ij y)
      (C.projectiveSectionLocalCoefficient base M ij i)
  refine ⟨c, C.projectiveSectionLocalEvaluatedCoefficient_ne_zero
    base M ij y, ?_⟩
  intro a
  exact C.projectiveSectionLocalBasisCoordinate_linearCombination_eq_zero
    base M ij y a

instance isClosedImmersion_projectiveSectionLocalZeroSubschemeι
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    IsClosedImmersion (C.projectiveSectionLocalZeroSubschemeι base M ij) := by
  unfold projectiveSectionLocalZeroSubschemeι
  infer_instance

/-- Intersection of two arbitrary affine product charts in the full
surface--projective-section ambient. -/
noncomputable abbrev projectiveSectionOpenCoverOverlap
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) : Scheme.{u} :=
  pullback ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)

/-- The left projection from a product-chart overlap is an open immersion. -/
instance isOpenImmersion_projectiveSectionOpenCoverOverlap_fst
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    IsOpenImmersion (pullback.fst
      ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl)) := by
  letI : IsOpenImmersion ((C.projectiveSectionOpenCover base M).f kl) :=
    (C.projectiveSectionOpenCover base M).map_prop kl
  infer_instance

/-- The right projection from a product-chart overlap is an open immersion. -/
instance isOpenImmersion_projectiveSectionOpenCoverOverlap_snd
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    IsOpenImmersion (pullback.snd
      ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl)) := by
  letI : IsOpenImmersion ((C.projectiveSectionOpenCover base M).f ij) :=
    (C.projectiveSectionOpenCover base M).map_prop ij
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- A refined product-chart inclusion followed by the ambient surface
projection is its originally defined surface projection. -/
theorem projectiveSectionOpenCover_f_comp_ambientFst
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionOpenCover base M).f ij ≫
        pullback.fst base
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M) =
      C.projectiveSectionOpenCoverToSurface base M ij := by
  change C.openCover.I₀ ×
    (schemeModuleGlobalSectionsProjectiveParameterChartCover base M).openCover.I₀ at ij
  simp only [projectiveSectionOpenCover, Scheme.Pullback.openCoverOfLeftRight_f]
  change (pullback.lift _ _ _) ≫ _ = _
  rw [pullback.lift_fst]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A refined product-chart inclusion followed by the ambient parameter
projection is its normalized parameter-chart projection followed by the
standard chart inclusion. -/
theorem projectiveSectionOpenCover_f_comp_ambientSnd
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij : (C.projectiveSectionOpenCover base M).I₀) :
    (C.projectiveSectionOpenCover base M).f ij ≫
        pullback.snd base
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M) =
      C.projectiveSectionOpenCoverToParameterChart base M ij ≫
        finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) ij.2 := by
  rcases ij with ⟨i, j⟩
  change (Scheme.Pullback.openCoverOfLeftRight C.openCover
      (schemeModuleGlobalSectionsProjectiveParameterChartCover base M).openCover
      base (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).f (i, j) ≫ _ = _
  rw [Scheme.Pullback.openCoverOfLeftRight_f]
  change (pullback.lift _ _ _) ≫ _ = _
  erw [pullback.lift_snd]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The two maps from a product-chart overlap to the original surface are
equal. -/
theorem projectiveSectionOpenCoverOverlap_toSurface_eq
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
        ((C.projectiveSectionOpenCover base M).f kl) ≫
          C.projectiveSectionOpenCoverToSurface base M ij =
      pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
        ((C.projectiveSectionOpenCover base M).f kl) ≫
          C.projectiveSectionOpenCoverToSurface base M kl := by
  rw [← C.projectiveSectionOpenCover_f_comp_ambientFst base M ij,
    ← C.projectiveSectionOpenCover_f_comp_ambientFst base M kl]
  rw [← Category.assoc, ← Category.assoc, pullback.condition]

/-- Parameter-chart map from a refined overlap through its left member. -/
noncomputable abbrev projectiveSectionOpenCoverOverlapToLeftParameterChart
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlap base M ij kl ⟶
      finiteDimensionalProjectiveChart K
        (SchemeModuleGlobalSectionsOver base M) ij.2 :=
  pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl) ≫
    C.projectiveSectionOpenCoverToParameterChart base M ij

/-- Parameter-chart map from a refined overlap through its right member. -/
noncomputable abbrev projectiveSectionOpenCoverOverlapToRightParameterChart
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlap base M ij kl ⟶
      finiteDimensionalProjectiveChart K
        (SchemeModuleGlobalSectionsOver base M) kl.2 :=
  pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl) ≫
    C.projectiveSectionOpenCoverToParameterChart base M kl

set_option backward.isDefEq.respectTransparency false in
/-- The left and right parameter maps of a refined overlap agree after the
standard projective-chart inclusions. -/
theorem projectiveSectionOpenCoverOverlap_toParameter_condition
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapToLeftParameterChart base M ij kl ≫
        finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) ij.2 =
      C.projectiveSectionOpenCoverOverlapToRightParameterChart base M ij kl ≫
        finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) kl.2 := by
  change
    (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
        ((C.projectiveSectionOpenCover base M).f kl) ≫
      C.projectiveSectionOpenCoverToParameterChart base M ij) ≫
        finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) ij.2 =
    (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
        ((C.projectiveSectionOpenCover base M).f kl) ≫
      C.projectiveSectionOpenCoverToParameterChart base M kl) ≫
        finiteDimensionalProjectiveChartι K
          (SchemeModuleGlobalSectionsOver base M) kl.2
  rw [Category.assoc,
    ← C.projectiveSectionOpenCover_f_comp_ambientSnd base M ij,
    ← Category.assoc, pullback.condition, Category.assoc,
    C.projectiveSectionOpenCover_f_comp_ambientSnd base M kl]
  simp only [Category.assoc]

/-- Map from an arbitrary refined overlap to the explicit intersection of
its two normalized projective parameter charts. -/
noncomputable def projectiveSectionOpenCoverOverlapToParameterOverlap
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlap base M ij kl ⟶
      schemeModuleProjectiveSectionOverlap base M ij.2 kl.2 :=
  (isPullback_chartOverlap
      (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base M)) ij.2 kl.2).lift
    (C.projectiveSectionOpenCoverOverlapToLeftParameterChart base M ij kl)
    (C.projectiveSectionOpenCoverOverlapToRightParameterChart base M ij kl)
    (by
      change C.projectiveSectionOpenCoverOverlapToLeftParameterChart base M ij kl ≫
          finiteDimensionalProjectiveChartι K
            (SchemeModuleGlobalSectionsOver base M) ij.2 =
        C.projectiveSectionOpenCoverOverlapToRightParameterChart base M ij kl ≫
          finiteDimensionalProjectiveChartι K
            (SchemeModuleGlobalSectionsOver base M) kl.2
      exact C.projectiveSectionOpenCoverOverlap_toParameter_condition base M ij kl)

/-- The overlap-parameter map recovers the left normalized chart map. -/
theorem projectiveSectionOpenCoverOverlapToParameterOverlap_comp_left
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapToParameterOverlap base M ij kl ≫
        Spec.map (CommRingCat.ofHom
          (chartOverlapLeftMap
            (finiteDimensionalProjectiveIdeal K
              (SchemeModuleGlobalSectionsOver base M)) ij.2 kl.2)) =
      C.projectiveSectionOpenCoverOverlapToLeftParameterChart base M ij kl := by
  exact (isPullback_chartOverlap
    (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver base M)) ij.2 kl.2).lift_fst _ _ _

/-- The overlap-parameter map recovers the right normalized chart map. -/
theorem projectiveSectionOpenCoverOverlapToParameterOverlap_comp_right
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    C.projectiveSectionOpenCoverOverlapToParameterOverlap base M ij kl ≫
        Spec.map (CommRingCat.ofHom
          (chartOverlapRightMap
            (finiteDimensionalProjectiveIdeal K
              (SchemeModuleGlobalSectionsOver base M)) ij.2 kl.2)) =
      C.projectiveSectionOpenCoverOverlapToRightParameterChart base M ij kl := by
  exact (isPullback_chartOverlap
    (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver base M)) ij.2 kl.2).lift_snd _ _ _

/-- The inverse normalized-coordinate transition on an arbitrary refined
product-chart overlap. -/
noncomputable def projectiveSectionOpenCoverOverlapUnit
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    Γ(C.projectiveSectionOpenCoverOverlap base M ij kl, ⊤) :=
  affineFunctionHom
    (C.projectiveSectionOpenCoverOverlapToParameterOverlap base M ij kl)
    (↑((chartOverlapUnit
      (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base M)) ij.2 kl.2)⁻¹))

/-- The refined-overlap transition function is invertible. -/
theorem isUnit_projectiveSectionOpenCoverOverlapUnit
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    IsUnit (C.projectiveSectionOpenCoverOverlapUnit base M ij kl) := by
  unfold projectiveSectionOpenCoverOverlapUnit
  exact ((chartOverlapUnit
    (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver base M)) ij.2 kl.2)⁻¹).isUnit.map _

/-- A left-chart normalized coefficient restricted to an arbitrary refined
overlap. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftCoefficient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀)
    (i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    Γ(C.projectiveSectionOpenCoverOverlap base M ij kl, ⊤) :=
  (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)).appTop.hom
      (C.projectiveSectionLocalCoefficient base M ij i)

/-- A right-chart normalized coefficient restricted to an arbitrary refined
overlap. -/
noncomputable def projectiveSectionOpenCoverOverlapRightCoefficient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀)
    (i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    Γ(C.projectiveSectionOpenCoverOverlap base M ij kl, ⊤) :=
  (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)).appTop.hom
      (C.projectiveSectionLocalCoefficient base M kl i)

set_option backward.isDefEq.respectTransparency false in
/-- Every restricted left coefficient is the common transition unit times
the corresponding restricted right coefficient. -/
theorem projectiveSectionOpenCoverOverlap_coefficient_relation
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀)
    (i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    C.projectiveSectionOpenCoverOverlapLeftCoefficient base M ij kl i =
      C.projectiveSectionOpenCoverOverlapUnit base M ij kl *
        C.projectiveSectionOpenCoverOverlapRightCoefficient base M ij kl i := by
  let V := SchemeModuleGlobalSectionsOver base M
  let J := finiteDimensionalProjectiveIdeal K V
  let qL := C.projectiveSectionOpenCoverOverlapToLeftParameterChart base M ij kl
  let qR := C.projectiveSectionOpenCoverOverlapToRightParameterChart base M ij kl
  let h := C.projectiveSectionOpenCoverOverlapToParameterOverlap base M ij kl
  change affineFunctionHom qL (chartCoordinate J ij.2 i) =
    affineFunctionHom h (↑((chartOverlapUnit J ij.2 kl.2)⁻¹)) *
      affineFunctionHom qR (chartCoordinate J kl.2 i)
  calc
    affineFunctionHom qL (chartCoordinate J ij.2 i) =
        affineFunctionHom (h ≫ Spec.map
          (CommRingCat.ofHom (chartOverlapLeftMap J ij.2 kl.2)))
          (chartCoordinate J ij.2 i) := by
      rw [C.projectiveSectionOpenCoverOverlapToParameterOverlap_comp_left base M ij kl]
    _ = affineFunctionHom h
        (chartOverlapLeftMap J ij.2 kl.2 (chartCoordinate J ij.2 i)) :=
      RingHom.congr_fun
        (affineFunctionHom_comp_Spec h (chartOverlapLeftMap J ij.2 kl.2)) _
    _ = affineFunctionHom h
        (↑((chartOverlapUnit J ij.2 kl.2)⁻¹) *
          chartOverlapRightMap J ij.2 kl.2 (chartCoordinate J kl.2 i)) := by
      rw [chartOverlap_coordinate_relation]
    _ = affineFunctionHom h (↑((chartOverlapUnit J ij.2 kl.2)⁻¹)) *
        affineFunctionHom h
          (chartOverlapRightMap J ij.2 kl.2 (chartCoordinate J kl.2 i)) := by
      rw [map_mul]
    _ = affineFunctionHom h (↑((chartOverlapUnit J ij.2 kl.2)⁻¹)) *
        affineFunctionHom (h ≫ Spec.map
          (CommRingCat.ofHom (chartOverlapRightMap J ij.2 kl.2)))
          (chartCoordinate J kl.2 i) := by
      exact congrArg
        (fun z => affineFunctionHom h
          (↑((chartOverlapUnit J ij.2 kl.2)⁻¹)) * z)
        (RingHom.congr_fun
          (affineFunctionHom_comp_Spec h
            (chartOverlapRightMap J ij.2 kl.2))
          (chartCoordinate J kl.2 i)).symm
    _ = affineFunctionHom h (↑((chartOverlapUnit J ij.2 kl.2)⁻¹)) *
        affineFunctionHom qR (chartCoordinate J kl.2 i) := by
      rw [C.projectiveSectionOpenCoverOverlapToParameterOverlap_comp_right base M ij kl]

/-- The left-normalized overlap equation, expressed in the pullback module
whose surface map is the right composite. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftUniversalSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  parameterizedSchemeModuleSection base M
    (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
        ((C.projectiveSectionOpenCover base M).f kl) ≫
      C.projectiveSectionOpenCoverToSurface base M kl)
    (C.projectiveSectionOpenCoverOverlapLeftCoefficient base M ij kl)
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M))

/-- The right-normalized overlap equation in the same pullback module. -/
noncomputable def projectiveSectionOpenCoverOverlapRightUniversalSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :=
  parameterizedSchemeModuleSection base M
    (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
        ((C.projectiveSectionOpenCover base M).f kl) ≫
      C.projectiveSectionOpenCoverToSurface base M kl)
    (C.projectiveSectionOpenCoverOverlapRightCoefficient base M ij kl)
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M))

/-- On every refined product-chart overlap, the two normalized universal
equations differ by the explicit invertible transition scalar. -/
theorem projectiveSectionOpenCoverOverlap_universalSection_commonScale
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    BundleSectionZeroLocus.scaleSection
      (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
        (C.projectiveSectionOpenCoverOverlapUnit base M ij kl))
      (C.projectiveSectionOpenCoverOverlapRightUniversalSection base M ij kl) =
        C.projectiveSectionOpenCoverOverlapLeftUniversalSection base M ij kl := by
  unfold projectiveSectionOpenCoverOverlapRightUniversalSection
    projectiveSectionOpenCoverOverlapLeftUniversalSection
    parameterizedSchemeModuleSection
  rw [finiteLinearCombinationSections_commonScale]
  congr 1
  funext i
  exact (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction_mul
      (X := C.projectiveSectionOpenCoverOverlap base M ij kl)
      (C.projectiveSectionOpenCoverOverlapUnit base M ij kl)
      (C.projectiveSectionOpenCoverOverlapRightCoefficient base M ij kl i)).symm.trans
    (congrArg
      (fun r => BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
        (X := C.projectiveSectionOpenCoverOverlap base M ij kl) r)
      (C.projectiveSectionOpenCoverOverlap_coefficient_relation base M ij kl i).symm)

/-- The scalar endomorphism relating the refined-overlap equations is an
isomorphism. -/
theorem isIso_projectiveSectionOpenCoverOverlapUnitCoefficient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    IsIso (BundleSectionZeroLocus.unitEndomorphismOfRegularFunction
      (C.projectiveSectionOpenCoverOverlapUnit base M ij kl)) :=
  BundleSectionZeroLocus.isIso_unitEndomorphismOfRegularFunction_of_isUnit _
    (C.isUnit_projectiveSectionOpenCoverOverlapUnit base M ij kl)

/-- In any free presentation of the common overlap module, the two transported
normalized universal equations define the same coordinate ideal. -/
theorem projectiveSectionOpenCoverOverlap_commonZeroIdeal_eq
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀)
    (J : Type u)
    (e : SheafOfModules.free
      (R := (C.projectiveSectionOpenCoverOverlap base M ij kl).ringCatSheaf) J ≅
      (Scheme.Modules.pullback
        (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl) ≫
          C.projectiveSectionOpenCoverToSurface base M kl)).obj M) :
    BundleSectionZeroLocus.sectionZeroIdealOfFreeIso J e
        (C.projectiveSectionOpenCoverOverlapLeftUniversalSection base M ij kl) =
      BundleSectionZeroLocus.sectionZeroIdealOfFreeIso J e
        (C.projectiveSectionOpenCoverOverlapRightUniversalSection base M ij kl) := by
  letI := C.isIso_projectiveSectionOpenCoverOverlapUnitCoefficient base M ij kl
  rw [← C.projectiveSectionOpenCoverOverlap_universalSection_commonScale
    base M ij kl]
  exact BundleSectionZeroLocus.sectionZeroIdealOfFreeIso_scaleSection_eq_of_isIso
    J e _ _

set_option backward.isDefEq.respectTransparency false in
/-- Transport from the restricted left local module to the common overlap
module presented using the right surface composite. -/
noncomputable def projectiveSectionOpenCoverOverlapLeftToCommonModuleIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (Scheme.Modules.restrictFunctor
      (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
        ((C.projectiveSectionOpenCover base M).f kl))).obj
        (C.projectiveSectionLocalModule base M ij) ≅
      (Scheme.Modules.pullback
        (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
            ((C.projectiveSectionOpenCover base M).f kl) ≫
          C.projectiveSectionOpenCoverToSurface base M kl)).obj M :=
  (Scheme.Modules.restrictFunctorIsoPullback
    (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl))).app
        (C.projectiveSectionLocalModule base M ij) ≪≫
  (Scheme.Modules.pullbackComp
    (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl))
    (C.projectiveSectionOpenCoverToSurface base M ij)).app M ≪≫
  (Scheme.Modules.pullbackCongr
    (C.projectiveSectionOpenCoverOverlap_toSurface_eq base M ij kl)).app M

set_option backward.isDefEq.respectTransparency false in
/-- Transport from the restricted right local module to the common overlap
module. -/
noncomputable def projectiveSectionOpenCoverOverlapRightToCommonModuleIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (Scheme.Modules.restrictFunctor
      (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
        ((C.projectiveSectionOpenCover base M).f kl))).obj
        (C.projectiveSectionLocalModule base M kl) ≅
      (Scheme.Modules.pullback
        (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
            ((C.projectiveSectionOpenCover base M).f kl) ≫
          C.projectiveSectionOpenCoverToSurface base M kl)).obj M :=
  (Scheme.Modules.restrictFunctorIsoPullback
    (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl))).app
        (C.projectiveSectionLocalModule base M kl) ≪≫
  (Scheme.Modules.pullbackComp
    (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl))
    (C.projectiveSectionOpenCoverToSurface base M kl)).app M

set_option backward.isDefEq.respectTransparency false in
/-- Canonical identification of the two restrictions of the local bundle
models to an arbitrary product-chart overlap. -/
noncomputable def projectiveSectionOpenCoverOverlapModuleIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    (Scheme.Modules.restrictFunctor
      (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
        ((C.projectiveSectionOpenCover base M).f kl))).obj
        (C.projectiveSectionLocalModule base M ij) ≅
      (Scheme.Modules.restrictFunctor
        (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl))).obj
        (C.projectiveSectionLocalModule base M kl) :=
  C.projectiveSectionOpenCoverOverlapLeftToCommonModuleIso base M ij kl ≪≫
    (C.projectiveSectionOpenCoverOverlapRightToCommonModuleIso base M ij kl).symm

set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionOpenCoverOverlap_left_parameterized_pullback
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    let p := pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl)
    let q := C.projectiveSectionOpenCoverToSurface base M ij
    SheafOfModules.sectionsMap ((Scheme.Modules.pullbackComp p q).app M).hom
      (BundleSectionZeroLocus.pullbackSection p
        (C.projectiveSectionLocalModule base M ij)
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison p)
        (C.projectiveSectionLocalUniversalSection base M ij)) =
      parameterizedSchemeModuleSection base M (p ≫ q)
        (C.projectiveSectionOpenCoverOverlapLeftCoefficient base M ij kl)
        (Module.finBasis K (SchemeModuleGlobalSectionsOver base M)) := by
  exact parameterizedSchemeModuleSection_pullback base M
    (C.projectiveSectionOpenCoverToSurface base M ij)
    (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl))
    (C.projectiveSectionLocalCoefficient base M ij)
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M))

set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionOpenCoverOverlap_left_parameterized_congr
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    let p := pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl)
    let q := C.projectiveSectionOpenCoverToSurface base M ij
    let h := C.projectiveSectionOpenCoverOverlap_toSurface_eq base M ij kl
    SheafOfModules.sectionsMap ((Scheme.Modules.pullbackCongr h).app M).hom
      (parameterizedSchemeModuleSection base M (p ≫ q)
        (C.projectiveSectionOpenCoverOverlapLeftCoefficient base M ij kl)
        (Module.finBasis K (SchemeModuleGlobalSectionsOver base M))) =
      C.projectiveSectionOpenCoverOverlapLeftUniversalSection base M ij kl := by
  exact parameterizedSchemeModuleSection_pullbackCongr base M _ _
    (C.projectiveSectionOpenCoverOverlap_toSurface_eq base M ij kl)
    (C.projectiveSectionOpenCoverOverlapLeftCoefficient base M ij kl)
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M))

set_option backward.isDefEq.respectTransparency false in
theorem projectiveSectionOpenCoverOverlap_right_parameterized_pullback
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    let p := pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl)
    let q := C.projectiveSectionOpenCoverToSurface base M kl
    SheafOfModules.sectionsMap ((Scheme.Modules.pullbackComp p q).app M).hom
      (BundleSectionZeroLocus.pullbackSection p
        (C.projectiveSectionLocalModule base M kl)
        (BundleSectionZeroLocus.isIso_pullbackUnitComparison p)
        (C.projectiveSectionLocalUniversalSection base M kl)) =
      C.projectiveSectionOpenCoverOverlapRightUniversalSection base M ij kl := by
  exact parameterizedSchemeModuleSection_pullback base M
    (C.projectiveSectionOpenCoverToSurface base M kl)
    (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl))
    (C.projectiveSectionLocalCoefficient base M kl)
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M))

/-
set_option backward.isDefEq.respectTransparency false in
/-- Restricting the left local universal section and transporting it to the
common overlap module gives the left-normalized common equation. -/
theorem projectiveSectionOpenCoverOverlap_left_section_transport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    SheafOfModules.sectionsMap
      (C.projectiveSectionOpenCoverOverlapLeftToCommonModuleIso
        base M ij kl).hom
      (BundleSectionZeroLocus.restrictModuleSection
        (pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl))
        (C.projectiveSectionLocalModule base M ij)
        (C.projectiveSectionLocalUniversalSection base M ij)) =
      C.projectiveSectionOpenCoverOverlapLeftUniversalSection base M ij kl := by
  let p := pullback.fst ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  let q := C.projectiveSectionOpenCoverToSurface base M ij
  let r := pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
      ((C.projectiveSectionOpenCover base M).f kl) ≫
    C.projectiveSectionOpenCoverToSurface base M kl
  let A := (Scheme.Modules.restrictFunctorIsoPullback p).app
    (C.projectiveSectionLocalModule base M ij)
  let B := (Scheme.Modules.pullbackComp p q).app M
  let H := (Scheme.Modules.pullbackCongr
    (C.projectiveSectionOpenCoverOverlap_toSurface_eq base M ij kl)).app M
  let e := C.projectiveSectionOpenCoverOverlapLeftToCommonModuleIso base M ij kl
  let s := C.projectiveSectionLocalUniversalSection base M ij
  let sC := BundleSectionZeroLocus.restrictModuleSection p
    (C.projectiveSectionLocalModule base M ij) s
  have he : e.hom = A.hom ≫ B.hom ≫ H.hom := by
    rfl
  calc
    SheafOfModules.sectionsMap e.hom sC =
        SheafOfModules.sectionsMap H.hom
          (SheafOfModules.sectionsMap B.hom
            (SheafOfModules.sectionsMap A.hom sC)) := by
      rw [he, SheafOfModules.sectionsMap_comp,
        SheafOfModules.sectionsMap_comp]
    _ = SheafOfModules.sectionsMap H.hom
          (SheafOfModules.sectionsMap B.hom
            (BundleSectionZeroLocus.pullbackSection p
              (C.projectiveSectionLocalModule base M ij)
              (BundleSectionZeroLocus.isIso_pullbackUnitComparison p) s)) := by
      exact congrArg
        (fun z => SheafOfModules.sectionsMap H.hom
          (SheafOfModules.sectionsMap B.hom z))
        (BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection p
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison p) s)
    _ = SheafOfModules.sectionsMap H.hom
          (parameterizedSchemeModuleSection base M (p ≫ q)
            (C.projectiveSectionOpenCoverOverlapLeftCoefficient base M ij kl)
            (Module.finBasis K (SchemeModuleGlobalSectionsOver base M))) := by
      exact congrArg (SheafOfModules.sectionsMap H.hom)
        (C.projectiveSectionOpenCoverOverlap_left_parameterized_pullback
          base M ij kl)
    _ = C.projectiveSectionOpenCoverOverlapLeftUniversalSection base M ij kl := by
      exact C.projectiveSectionOpenCoverOverlap_left_parameterized_congr
        base M ij kl

set_option backward.isDefEq.respectTransparency false in
/-- The analogous transport statement for the right local universal
section. -/
theorem projectiveSectionOpenCoverOverlap_right_section_transport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    SheafOfModules.sectionsMap
      (C.projectiveSectionOpenCoverOverlapRightToCommonModuleIso
        base M ij kl).hom
      (BundleSectionZeroLocus.restrictModuleSection
        (pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
          ((C.projectiveSectionOpenCover base M).f kl))
        (C.projectiveSectionLocalModule base M kl)
        (C.projectiveSectionLocalUniversalSection base M kl)) =
      C.projectiveSectionOpenCoverOverlapRightUniversalSection base M ij kl := by
  let p := pullback.snd ((C.projectiveSectionOpenCover base M).f ij)
    ((C.projectiveSectionOpenCover base M).f kl)
  let q := C.projectiveSectionOpenCoverToSurface base M kl
  let A := (Scheme.Modules.restrictFunctorIsoPullback p).app
    (C.projectiveSectionLocalModule base M kl)
  let B := (Scheme.Modules.pullbackComp p q).app M
  let e := C.projectiveSectionOpenCoverOverlapRightToCommonModuleIso base M ij kl
  let s := C.projectiveSectionLocalUniversalSection base M kl
  let sC := BundleSectionZeroLocus.restrictModuleSection p
    (C.projectiveSectionLocalModule base M kl) s
  have he : e.hom = A.hom ≫ B.hom := by rfl
  calc
    SheafOfModules.sectionsMap e.hom sC =
        SheafOfModules.sectionsMap B.hom
          (SheafOfModules.sectionsMap A.hom sC) := by
      rw [he, SheafOfModules.sectionsMap_comp]
    _ = SheafOfModules.sectionsMap B.hom
          (BundleSectionZeroLocus.pullbackSection p
            (C.projectiveSectionLocalModule base M kl)
            (BundleSectionZeroLocus.isIso_pullbackUnitComparison p) s) := by
      exact congrArg (SheafOfModules.sectionsMap B.hom)
        (BundleSectionZeroLocus.restrictModuleSection_to_pullbackSection p
          (BundleSectionZeroLocus.isIso_pullbackUnitComparison p) s)
    _ = C.projectiveSectionOpenCoverOverlapRightUniversalSection base M ij kl := by
      exact C.projectiveSectionOpenCoverOverlap_right_parameterized_pullback
        base M ij kl

-/
/-- The complete ambient product is separated when the original surface is
separated over the coefficient field. -/
theorem projectiveSectionAmbient_isSeparated
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)] :
    (pullback base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).IsSeparated := by
  constructor
  change IsSeparated (terminal.from (pullback base
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M)))
  have hcomp : terminal.from (pullback base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)) =
      pullback.fst base
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M) ≫
        base ≫ terminal.from (Spec (.of K)) := by
    ext
  rw [hcomp]
  infer_instance

/-- An open immersion from an affine scheme to a separated scheme is affine. -/
theorem isAffineHom_openImmersion_of_affine_separated
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    [IsAffine Y] [Z.IsSeparated] : IsAffineHom f := by
  constructor
  intro U hU
  rw [← f.isAffineOpen_iff_of_isOpenImmersion,
    f.image_preimage_eq_opensRange_inf]
  exact (isAffineOpen_opensRange f).inf hU

/-- Pairwise intersections of the affine product charts are affine. -/
theorem projectiveSectionOpenCoverOverlap_affine
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} (C : SchemeModuleFiniteFreeAffineCover M I)
    (ij kl : (C.projectiveSectionOpenCover base M).I₀) :
    IsAffine (C.projectiveSectionOpenCoverOverlap base M ij kl) := by
  letI : (pullback base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).IsSeparated :=
    projectiveSectionAmbient_isSeparated base M
  letI : IsAffine ((C.projectiveSectionOpenCover base M).X ij) :=
    C.projectiveSectionOpenCover_affine base M ij
  letI : IsAffine ((C.projectiveSectionOpenCover base M).X kl) :=
    C.projectiveSectionOpenCover_affine base M kl
  letI : IsOpenImmersion ((C.projectiveSectionOpenCover base M).f kl) :=
    (C.projectiveSectionOpenCover base M).map_prop kl
  letI : IsAffineHom ((C.projectiveSectionOpenCover base M).f kl) :=
    isAffineHom_openImmersion_of_affine_separated _
  infer_instance

end SchemeModuleFiniteFreeAffineCover

end

end PfaffianDescent
