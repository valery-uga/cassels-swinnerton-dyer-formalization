import PfaffianDescent.VoisinFixedLinearSystemUniversalChart
import PfaffianDescent.BundleSectionZeroLocusNaturality
import AllCharacteristics.ProjectiveChartOverlap

/-!
# Overlaps of normalized universal sections

The normalized universal section of a finite-dimensional linear system is
defined separately on each standard chart of its projective parameter
space.  On the explicit intersection of two charts, all left normalized
coefficients are the corresponding right normalized coefficients multiplied
by one common invertible regular function.  Consequently the two universal
sections differ by that same invertible scalar.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
open BundleSectionZeroLocus

universe u

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The explicit intersection ring of two standard charts in the
projectivized space of global sections. -/
abbrev schemeModuleProjectiveSectionOverlapRing
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :=
  ChartOverlapRing
    (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver base M)) j l

/-- The explicit intersection of two normalized parameter charts. -/
noncomputable abbrev schemeModuleProjectiveSectionOverlap
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    Scheme.{u} :=
  Spec (.of (schemeModuleProjectiveSectionOverlapRing base M j l))

/-- Structure morphism of the intersection of two normalized parameter
charts.  It is written through the left chart; the overlap base-map theorem
shows that the right chart gives the same morphism. -/
noncomputable def schemeModuleProjectiveSectionOverlapToBase
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionOverlap base M j l ⟶ Spec (.of K) :=
  let V := SchemeModuleGlobalSectionsOver base M
  Spec.map (CommRingCat.ofHom
      (chartOverlapLeftMap (finiteDimensionalProjectiveIdeal K V) j l)) ≫
    finiteDimensionalProjectiveChartToBase K V j

/-- The right normalized chart induces the same structure morphism on the
explicit overlap. -/
theorem schemeModuleProjectiveSectionOverlapToBase_eq_right
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    Spec.map (CommRingCat.ofHom
        (chartOverlapRightMap
          (finiteDimensionalProjectiveIdeal K
            (SchemeModuleGlobalSectionsOver base M)) j l)) ≫
      finiteDimensionalProjectiveChartToBase K
        (SchemeModuleGlobalSectionsOver base M) l =
      schemeModuleProjectiveSectionOverlapToBase base M j l := by
  unfold schemeModuleProjectiveSectionOverlapToBase
    finiteDimensionalProjectiveChartToBase
  dsimp only
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro k
  exact (chartOverlapRightMap_baseMap
    (finiteDimensionalProjectiveIdeal K
      (SchemeModuleGlobalSectionsOver base M)) j l k).trans
    (chartOverlapLeftMap_baseMap
      (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base M)) j l k).symm

/-- The surface pulled to the common intersection of two parameter charts. -/
noncomputable abbrev schemeModuleProjectiveSectionOverlapAmbient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    Scheme.{u} :=
  pullback base (schemeModuleProjectiveSectionOverlapToBase base M j l)

/-- Restriction of the surface over the left normalized chart to the common
overlap. -/
noncomputable def schemeModuleProjectiveSectionOverlapAmbientToLeft
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionOverlapAmbient base M j l ⟶
      schemeModuleProjectiveSectionChartAmbient base M j :=
  let V := SchemeModuleGlobalSectionsOver base M
  let I := finiteDimensionalProjectiveIdeal K V
  pullback.map base (schemeModuleProjectiveSectionOverlapToBase base M j l)
    base (finiteDimensionalProjectiveChartToBase K V j)
    (𝟙 X) (Spec.map (CommRingCat.ofHom (chartOverlapLeftMap I j l)))
    (𝟙 (Spec (.of K))) (by simp)
    (by rfl)

/-- Restriction of the surface over the right normalized chart to the common
overlap. -/
noncomputable def schemeModuleProjectiveSectionOverlapAmbientToRight
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionOverlapAmbient base M j l ⟶
      schemeModuleProjectiveSectionChartAmbient base M l :=
  let V := SchemeModuleGlobalSectionsOver base M
  let I := finiteDimensionalProjectiveIdeal K V
  pullback.map base (schemeModuleProjectiveSectionOverlapToBase base M j l)
    base (finiteDimensionalProjectiveChartToBase K V l)
    (𝟙 X) (Spec.map (CommRingCat.ofHom (chartOverlapRightMap I j l)))
    (𝟙 (Spec (.of K))) (by simp)
    (by
      rw [Category.comp_id]
      exact (schemeModuleProjectiveSectionOverlapToBase_eq_right base M j l).symm)

instance schemeModuleProjectiveSectionOverlapAmbientToLeft_isOpenImmersion
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    IsOpenImmersion
      (schemeModuleProjectiveSectionOverlapAmbientToLeft base M j l) := by
  unfold schemeModuleProjectiveSectionOverlapAmbientToLeft
  apply Scheme.pullback_map_isOpenImmersion

instance schemeModuleProjectiveSectionOverlapAmbientToRight_isOpenImmersion
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    IsOpenImmersion
      (schemeModuleProjectiveSectionOverlapAmbientToRight base M j l) := by
  unfold schemeModuleProjectiveSectionOverlapAmbientToRight
  apply Scheme.pullback_map_isOpenImmersion

/-- The left overlap restriction is the identity on the underlying surface
factor. -/
theorem schemeModuleProjectiveSectionOverlapAmbientToLeft_fst
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionOverlapAmbientToLeft base M j l ≫
        pullback.fst base
          (finiteDimensionalProjectiveChartToBase K
            (SchemeModuleGlobalSectionsOver base M) j) =
      pullback.fst base
        (schemeModuleProjectiveSectionOverlapToBase base M j l) := by
  simp only [schemeModuleProjectiveSectionOverlapAmbientToLeft, pullback.map,
    pullback.lift_fst, Category.comp_id]

/-- The right overlap restriction is the identity on the underlying surface
factor. -/
theorem schemeModuleProjectiveSectionOverlapAmbientToRight_fst
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionOverlapAmbientToRight base M j l ≫
        pullback.fst base
          (finiteDimensionalProjectiveChartToBase K
            (SchemeModuleGlobalSectionsOver base M) l) =
      pullback.fst base
        (schemeModuleProjectiveSectionOverlapToBase base M j l) := by
  simp only [schemeModuleProjectiveSectionOverlapAmbientToRight, pullback.map,
    pullback.lift_fst, Category.comp_id]

/-- Canonical identification between the iterated pullback of the module
from the left chart and its direct pullback to the overlap ambient. -/
noncomputable def schemeModuleProjectiveSectionOverlapLeftModuleIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (Scheme.Modules.pullback
        (schemeModuleProjectiveSectionOverlapAmbientToLeft base M j l)).obj
      ((Scheme.Modules.pullback
        (pullback.fst base
          (finiteDimensionalProjectiveChartToBase K
            (SchemeModuleGlobalSectionsOver base M) j))).obj M) ≅
      (Scheme.Modules.pullback
        (pullback.fst base
          (schemeModuleProjectiveSectionOverlapToBase base M j l))).obj M :=
  (Scheme.Modules.pullbackComp
      (schemeModuleProjectiveSectionOverlapAmbientToLeft base M j l)
      (pullback.fst base
        (finiteDimensionalProjectiveChartToBase K
          (SchemeModuleGlobalSectionsOver base M) j))).app M ≪≫
    (Scheme.Modules.pullbackCongr
      (schemeModuleProjectiveSectionOverlapAmbientToLeft_fst base M j l)).app M

/-- Canonical identification between the iterated pullback of the module
from the right chart and its direct pullback to the overlap ambient. -/
noncomputable def schemeModuleProjectiveSectionOverlapRightModuleIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (Scheme.Modules.pullback
        (schemeModuleProjectiveSectionOverlapAmbientToRight base M j l)).obj
      ((Scheme.Modules.pullback
        (pullback.fst base
          (finiteDimensionalProjectiveChartToBase K
            (SchemeModuleGlobalSectionsOver base M) l))).obj M) ≅
      (Scheme.Modules.pullback
        (pullback.fst base
          (schemeModuleProjectiveSectionOverlapToBase base M j l))).obj M :=
  (Scheme.Modules.pullbackComp
      (schemeModuleProjectiveSectionOverlapAmbientToRight base M j l)
      (pullback.fst base
        (finiteDimensionalProjectiveChartToBase K
          (SchemeModuleGlobalSectionsOver base M) l))).app M ≪≫
    (Scheme.Modules.pullbackCongr
      (schemeModuleProjectiveSectionOverlapAmbientToRight_fst base M j l)).app M

/-- The module pulled from the surface to one normalized parameter chart. -/
noncomputable abbrev schemeModuleProjectiveSectionChartPulledModule
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :=
  (Scheme.Modules.pullback
    (pullback.fst base
      (finiteDimensionalProjectiveChartToBase K
        (SchemeModuleGlobalSectionsOver base M) j))).obj M

/-- The module pulled directly from the surface to a common parameter-chart
overlap. -/
noncomputable abbrev schemeModuleProjectiveSectionOverlapPulledModule
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :=
  (Scheme.Modules.pullback
    (pullback.fst base
      (schemeModuleProjectiveSectionOverlapToBase base M j l))).obj M

/-- One chosen basis section pulled to a normalized parameter chart. -/
noncomputable def schemeModuleProjectiveSectionChartBasisSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (schemeModuleProjectiveSectionChartPulledModule base M j).sections :=
  pullbackSection
    (pullback.fst base
      (finiteDimensionalProjectiveChartToBase K
        (SchemeModuleGlobalSectionsOver base M) j)) M
    (isIso_pullbackUnitComparison _)
    (schemeModuleGlobalSectionsOverEquivSections base M
      (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i))

/-- One chosen basis section pulled directly to a common overlap. -/
noncomputable def schemeModuleProjectiveSectionOverlapBasisSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (schemeModuleProjectiveSectionOverlapPulledModule base M j l).sections :=
  pullbackSection
    (pullback.fst base
      (schemeModuleProjectiveSectionOverlapToBase base M j l)) M
    (isIso_pullbackUnitComparison _)
    (schemeModuleGlobalSectionsOverEquivSections base M
      (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i))

/-- A left-chart basis section pulled once more to the common overlap. -/
noncomputable def schemeModuleProjectiveSectionOverlapLeftIteratedBasisSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    ((Scheme.Modules.pullback
      (schemeModuleProjectiveSectionOverlapAmbientToLeft base M j l)).obj
        (schemeModuleProjectiveSectionChartPulledModule base M j)).sections :=
  pullbackSection
    (schemeModuleProjectiveSectionOverlapAmbientToLeft base M j l)
    (schemeModuleProjectiveSectionChartPulledModule base M j)
    (isIso_pullbackUnitComparison _)
    (schemeModuleProjectiveSectionChartBasisSection base M j i)

/-- A right-chart basis section pulled once more to the common overlap. -/
noncomputable def schemeModuleProjectiveSectionOverlapRightIteratedBasisSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    ((Scheme.Modules.pullback
      (schemeModuleProjectiveSectionOverlapAmbientToRight base M j l)).obj
        (schemeModuleProjectiveSectionChartPulledModule base M l)).sections :=
  pullbackSection
    (schemeModuleProjectiveSectionOverlapAmbientToRight base M j l)
    (schemeModuleProjectiveSectionChartPulledModule base M l)
    (isIso_pullbackUnitComparison _)
    (schemeModuleProjectiveSectionChartBasisSection base M l i)

/-- Pulling one basis section through the left chart and then transporting
through the canonical pullback-composition isomorphism gives its direct
pullback to the common overlap. -/
theorem schemeModuleProjectiveSectionOverlapLeft_basisSection_transport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    SheafOfModules.sectionsMap
      (schemeModuleProjectiveSectionOverlapLeftModuleIso base M j l).hom
      (schemeModuleProjectiveSectionOverlapLeftIteratedBasisSection
        base M j l i) =
      schemeModuleProjectiveSectionOverlapBasisSection base M j l i := by
  let a := schemeModuleProjectiveSectionOverlapAmbientToLeft base M j l
  let g := pullback.fst base
    (finiteDimensionalProjectiveChartToBase K
      (SchemeModuleGlobalSectionsOver base M) j)
  let q := pullback.fst base
    (schemeModuleProjectiveSectionOverlapToBase base M j l)
  let h : a ≫ g = q :=
    schemeModuleProjectiveSectionOverlapAmbientToLeft_fst base M j l
  let s := schemeModuleGlobalSectionsOverEquivSections base M
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i)
  exact sectionsMap_pullbackComp_pullbackCongr_pullbackSection
    a g q h M (isIso_pullbackUnitComparison a)
    (isIso_pullbackUnitComparison g) (isIso_pullbackUnitComparison (a ≫ g))
    (isIso_pullbackUnitComparison q) s

/-- The analogous transport statement for one basis section through the
right normalized chart. -/
theorem schemeModuleProjectiveSectionOverlapRight_basisSection_transport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    SheafOfModules.sectionsMap
      (schemeModuleProjectiveSectionOverlapRightModuleIso base M j l).hom
      (schemeModuleProjectiveSectionOverlapRightIteratedBasisSection
        base M j l i) =
      schemeModuleProjectiveSectionOverlapBasisSection base M j l i := by
  let a := schemeModuleProjectiveSectionOverlapAmbientToRight base M j l
  let g := pullback.fst base
    (finiteDimensionalProjectiveChartToBase K
      (SchemeModuleGlobalSectionsOver base M) l)
  let q := pullback.fst base
    (schemeModuleProjectiveSectionOverlapToBase base M j l)
  let h : a ≫ g = q :=
    schemeModuleProjectiveSectionOverlapAmbientToRight_fst base M j l
  let s := schemeModuleGlobalSectionsOverEquivSections base M
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i)
  exact sectionsMap_pullbackComp_pullbackCongr_pullbackSection
    a g q h M (isIso_pullbackUnitComparison a)
    (isIso_pullbackUnitComparison g) (isIso_pullbackUnitComparison (a ≫ g))
    (isIso_pullbackUnitComparison q) s

/-- The left overlap restriction uses the explicit left projective-chart
ring map on the parameter factor. -/
theorem schemeModuleProjectiveSectionOverlapAmbientToLeft_snd
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionOverlapAmbientToLeft base M j l ≫
        pullback.snd base
          (finiteDimensionalProjectiveChartToBase K
            (SchemeModuleGlobalSectionsOver base M) j) =
      pullback.snd base
          (schemeModuleProjectiveSectionOverlapToBase base M j l) ≫
        Spec.map (CommRingCat.ofHom
          (chartOverlapLeftMap
            (finiteDimensionalProjectiveIdeal K
              (SchemeModuleGlobalSectionsOver base M)) j l)) := by
  simp only [schemeModuleProjectiveSectionOverlapAmbientToLeft, pullback.map,
    pullback.lift_snd]

/-- The right overlap restriction uses the explicit right projective-chart
ring map on the parameter factor. -/
theorem schemeModuleProjectiveSectionOverlapAmbientToRight_snd
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionOverlapAmbientToRight base M j l ≫
        pullback.snd base
          (finiteDimensionalProjectiveChartToBase K
            (SchemeModuleGlobalSectionsOver base M) l) =
      pullback.snd base
          (schemeModuleProjectiveSectionOverlapToBase base M j l) ≫
        Spec.map (CommRingCat.ofHom
          (chartOverlapRightMap
            (finiteDimensionalProjectiveIdeal K
              (SchemeModuleGlobalSectionsOver base M)) j l)) := by
  simp only [schemeModuleProjectiveSectionOverlapAmbientToRight, pullback.map,
    pullback.lift_snd]

/-- A homogeneous coordinate normalized on the left chart, restricted to
the common surface-over-parameter overlap. -/
noncomputable def schemeModuleProjectiveSectionOverlapLeftCoefficient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    Γ(schemeModuleProjectiveSectionOverlapAmbient base M j l, ⊤) :=
  let V := SchemeModuleGlobalSectionsOver base M
  let I := finiteDimensionalProjectiveIdeal K V
  let R := ChartOverlapRing I j l
  (pullback.snd base
      (schemeModuleProjectiveSectionOverlapToBase base M j l)).appTop.hom
    ((Scheme.ΓSpecIso (.of R)).inv.hom
      (chartOverlapLeftMap I j l (chartCoordinate I j i)))

/-- A homogeneous coordinate normalized on the right chart, restricted to
the common surface-over-parameter overlap. -/
noncomputable def schemeModuleProjectiveSectionOverlapRightCoefficient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    Γ(schemeModuleProjectiveSectionOverlapAmbient base M j l, ⊤) :=
  let V := SchemeModuleGlobalSectionsOver base M
  let I := finiteDimensionalProjectiveIdeal K V
  let R := ChartOverlapRing I j l
  (pullback.snd base
      (schemeModuleProjectiveSectionOverlapToBase base M j l)).appTop.hom
    ((Scheme.ΓSpecIso (.of R)).inv.hom
      (chartOverlapRightMap I j l (chartCoordinate I l i)))

/-- Pulling a left-chart coefficient to the overlap gives the coefficient
defined directly from the left overlap ring map. -/
theorem schemeModuleProjectiveSectionChartCoefficient_pullback_left
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (schemeModuleProjectiveSectionOverlapAmbientToLeft base M j l).appTop.hom
        (schemeModuleProjectiveSectionChartCoefficient base M j i) =
      schemeModuleProjectiveSectionOverlapLeftCoefficient base M j l i := by
  let V := SchemeModuleGlobalSectionsOver base M
  let I := finiteDimensionalProjectiveIdeal K V
  let p := pullback.snd base
    (finiteDimensionalProjectiveChartToBase K V j)
  let q := pullback.snd base
    (schemeModuleProjectiveSectionOverlapToBase base M j l)
  let a := schemeModuleProjectiveSectionOverlapAmbientToLeft base M j l
  change a.appTop.hom (affineFunctionHom p (chartCoordinate I j i)) =
    affineFunctionHom q (chartOverlapLeftMap I j l (chartCoordinate I j i))
  have hcomp := RingHom.congr_fun (affineFunctionHom_comp a p)
    (chartCoordinate I j i)
  refine hcomp.symm.trans ?_
  rw [schemeModuleProjectiveSectionOverlapAmbientToLeft_snd]
  exact RingHom.congr_fun
    (affineFunctionHom_comp_Spec q (chartOverlapLeftMap I j l))
    (chartCoordinate I j i)

/-- Pulling a right-chart coefficient to the overlap gives the coefficient
defined directly from the right overlap ring map. -/
theorem schemeModuleProjectiveSectionChartCoefficient_pullback_right
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (schemeModuleProjectiveSectionOverlapAmbientToRight base M j l).appTop.hom
        (schemeModuleProjectiveSectionChartCoefficient base M l i) =
      schemeModuleProjectiveSectionOverlapRightCoefficient base M j l i := by
  let V := SchemeModuleGlobalSectionsOver base M
  let I := finiteDimensionalProjectiveIdeal K V
  let p := pullback.snd base
    (finiteDimensionalProjectiveChartToBase K V l)
  let q := pullback.snd base
    (schemeModuleProjectiveSectionOverlapToBase base M j l)
  let a := schemeModuleProjectiveSectionOverlapAmbientToRight base M j l
  change a.appTop.hom (affineFunctionHom p (chartCoordinate I l i)) =
    affineFunctionHom q (chartOverlapRightMap I j l (chartCoordinate I l i))
  have hcomp := RingHom.congr_fun (affineFunctionHom_comp a p)
    (chartCoordinate I l i)
  refine hcomp.symm.trans ?_
  rw [schemeModuleProjectiveSectionOverlapAmbientToRight_snd]
  exact RingHom.congr_fun
    (affineFunctionHom_comp_Spec q (chartOverlapRightMap I j l))
    (chartCoordinate I l i)

/-- One summand of the universal section on a normalized chart. -/
noncomputable def schemeModuleProjectiveSectionChartUniversalTerm
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (schemeModuleProjectiveSectionChartPulledModule base M j).sections :=
  scaleSection
    (unitEndomorphismOfRegularFunction
      (schemeModuleProjectiveSectionChartCoefficient base M j i))
    (schemeModuleProjectiveSectionChartBasisSection base M j i)

/-- One left-normalized summand of the universal section on a common
overlap. -/
noncomputable def schemeModuleProjectiveSectionOverlapLeftUniversalTerm
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (schemeModuleProjectiveSectionOverlapPulledModule base M j l).sections :=
  scaleSection
    (unitEndomorphismOfRegularFunction
      (schemeModuleProjectiveSectionOverlapLeftCoefficient base M j l i))
    (schemeModuleProjectiveSectionOverlapBasisSection base M j l i)

/-- One right-normalized summand of the universal section on a common
overlap. -/
noncomputable def schemeModuleProjectiveSectionOverlapRightUniversalTerm
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (schemeModuleProjectiveSectionOverlapPulledModule base M j l).sections :=
  scaleSection
    (unitEndomorphismOfRegularFunction
      (schemeModuleProjectiveSectionOverlapRightCoefficient base M j l i))
    (schemeModuleProjectiveSectionOverlapBasisSection base M j l i)

/-- Pull one left-chart universal summand to the common overlap. -/
noncomputable def
    schemeModuleProjectiveSectionOverlapLeftIteratedUniversalTerm
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    ((Scheme.Modules.pullback
      (schemeModuleProjectiveSectionOverlapAmbientToLeft base M j l)).obj
        (schemeModuleProjectiveSectionChartPulledModule base M j)).sections :=
  pullbackSection
    (schemeModuleProjectiveSectionOverlapAmbientToLeft base M j l)
    (schemeModuleProjectiveSectionChartPulledModule base M j)
    (isIso_pullbackUnitComparison _)
    (schemeModuleProjectiveSectionChartUniversalTerm base M j i)

/-- Pull one right-chart universal summand to the common overlap. -/
noncomputable def
    schemeModuleProjectiveSectionOverlapRightIteratedUniversalTerm
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    ((Scheme.Modules.pullback
      (schemeModuleProjectiveSectionOverlapAmbientToRight base M j l)).obj
        (schemeModuleProjectiveSectionChartPulledModule base M l)).sections :=
  pullbackSection
    (schemeModuleProjectiveSectionOverlapAmbientToRight base M j l)
    (schemeModuleProjectiveSectionChartPulledModule base M l)
    (isIso_pullbackUnitComparison _)
    (schemeModuleProjectiveSectionChartUniversalTerm base M l i)

/-- Each left-chart universal summand restricts to the corresponding
left-normalized common-overlap summand. -/
theorem schemeModuleProjectiveSectionOverlapLeft_universalTerm_transport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    SheafOfModules.sectionsMap
      (schemeModuleProjectiveSectionOverlapLeftModuleIso base M j l).hom
      (schemeModuleProjectiveSectionOverlapLeftIteratedUniversalTerm
        base M j l i) =
      schemeModuleProjectiveSectionOverlapLeftUniversalTerm base M j l i := by
  unfold schemeModuleProjectiveSectionOverlapLeftIteratedUniversalTerm
    schemeModuleProjectiveSectionChartUniversalTerm
    schemeModuleProjectiveSectionOverlapLeftUniversalTerm
  rw [pullbackSection_scaleSection, sectionsMap_scaleSection,
    pullbackUnitEndomorphismOfRegularFunction_eq_appTop,
    schemeModuleProjectiveSectionChartCoefficient_pullback_left]
  exact congrArg
    (scaleSection (unitEndomorphismOfRegularFunction
      (schemeModuleProjectiveSectionOverlapLeftCoefficient base M j l i)))
    (schemeModuleProjectiveSectionOverlapLeft_basisSection_transport
      base M j l i)

/-- Each right-chart universal summand restricts to the corresponding
right-normalized common-overlap summand. -/
theorem schemeModuleProjectiveSectionOverlapRight_universalTerm_transport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    SheafOfModules.sectionsMap
      (schemeModuleProjectiveSectionOverlapRightModuleIso base M j l).hom
      (schemeModuleProjectiveSectionOverlapRightIteratedUniversalTerm
        base M j l i) =
      schemeModuleProjectiveSectionOverlapRightUniversalTerm base M j l i := by
  unfold schemeModuleProjectiveSectionOverlapRightIteratedUniversalTerm
    schemeModuleProjectiveSectionChartUniversalTerm
    schemeModuleProjectiveSectionOverlapRightUniversalTerm
  rw [pullbackSection_scaleSection, sectionsMap_scaleSection,
    pullbackUnitEndomorphismOfRegularFunction_eq_appTop,
    schemeModuleProjectiveSectionChartCoefficient_pullback_right]
  exact congrArg
    (scaleSection (unitEndomorphismOfRegularFunction
      (schemeModuleProjectiveSectionOverlapRightCoefficient base M j l i)))
    (schemeModuleProjectiveSectionOverlapRight_basisSection_transport
      base M j l i)

/-- The chartwise universal section is the finite sum of its named
coefficient-times-basis summands. -/
theorem schemeModuleProjectiveSectionChartUniversalSection_eq_sumTerms
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionChartUniversalSection base M j =
      sumSections (fun i =>
        schemeModuleProjectiveSectionChartUniversalTerm base M j i) := by
  rfl

/-- The inverse projective transition coordinate, pulled to the common
surface-over-parameter overlap. -/
noncomputable def schemeModuleProjectiveSectionOverlapUnit
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    Γ(schemeModuleProjectiveSectionOverlapAmbient base M j l, ⊤) :=
  let V := SchemeModuleGlobalSectionsOver base M
  let I := finiteDimensionalProjectiveIdeal K V
  let R := ChartOverlapRing I j l
  (pullback.snd base
      (schemeModuleProjectiveSectionOverlapToBase base M j l)).appTop.hom
    ((Scheme.ΓSpecIso (.of R)).inv.hom
      (↑((chartOverlapUnit I j l)⁻¹) : R))

/-- Every normalized coordinate on the left is the common inverse
transition unit times the corresponding normalized coordinate on the
right. -/
theorem schemeModuleProjectiveSectionOverlap_coefficient_relation
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l i : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionOverlapLeftCoefficient base M j l i =
      schemeModuleProjectiveSectionOverlapUnit base M j l *
        schemeModuleProjectiveSectionOverlapRightCoefficient base M j l i := by
  unfold schemeModuleProjectiveSectionOverlapLeftCoefficient
    schemeModuleProjectiveSectionOverlapRightCoefficient
    schemeModuleProjectiveSectionOverlapUnit
  dsimp only
  rw [chartOverlap_coordinate_relation, map_mul, map_mul]

/-- The projective transition function remains a unit after pullback to the
surface-over-parameter overlap. -/
theorem isUnit_schemeModuleProjectiveSectionOverlapUnit
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    IsUnit (schemeModuleProjectiveSectionOverlapUnit base M j l) := by
  unfold schemeModuleProjectiveSectionOverlapUnit
  dsimp only
  exact ((chartOverlapUnit
      (finiteDimensionalProjectiveIdeal K
        (SchemeModuleGlobalSectionsOver base M)) j l)⁻¹).isUnit.map _ |>.map _

/-- The universal section written with the left normalized coordinates on
the common overlap. -/
noncomputable def schemeModuleProjectiveSectionOverlapLeftUniversalSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    ((Scheme.Modules.pullback
      (pullback.fst base
        (schemeModuleProjectiveSectionOverlapToBase base M j l))).obj M).sections :=
  parameterizedSchemeModuleSection
    (ι := Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    base M
    (pullback.fst base
      (schemeModuleProjectiveSectionOverlapToBase base M j l))
    (schemeModuleProjectiveSectionOverlapLeftCoefficient base M j l)
    (fun i => Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i)

/-- The universal section written with the right normalized coordinates on
the common overlap. -/
noncomputable def schemeModuleProjectiveSectionOverlapRightUniversalSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    ((Scheme.Modules.pullback
      (pullback.fst base
        (schemeModuleProjectiveSectionOverlapToBase base M j l))).obj M).sections :=
  parameterizedSchemeModuleSection
    (ι := Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    base M
    (pullback.fst base
      (schemeModuleProjectiveSectionOverlapToBase base M j l))
    (schemeModuleProjectiveSectionOverlapRightCoefficient base M j l)
    (fun i => Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i)

/-- The left common-overlap universal section is the finite sum of its named
summands. -/
theorem schemeModuleProjectiveSectionOverlapLeftUniversalSection_eq_sumTerms
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionOverlapLeftUniversalSection base M j l =
      sumSections (fun i =>
        schemeModuleProjectiveSectionOverlapLeftUniversalTerm base M j l i) := by
  rfl

/-- The right common-overlap universal section is the finite sum of its named
summands. -/
theorem schemeModuleProjectiveSectionOverlapRightUniversalSection_eq_sumTerms
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionOverlapRightUniversalSection base M j l =
      sumSections (fun i =>
        schemeModuleProjectiveSectionOverlapRightUniversalTerm base M j l i) := by
  rfl

/-- The termwise pullback-and-transport of the left chart equation. -/
noncomputable def
    schemeModuleProjectiveSectionOverlapLeftTransportedUniversalSum
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (schemeModuleProjectiveSectionOverlapPulledModule base M j l).sections :=
  sumSections (fun i => SheafOfModules.sectionsMap
    (schemeModuleProjectiveSectionOverlapLeftModuleIso base M j l).hom
    (schemeModuleProjectiveSectionOverlapLeftIteratedUniversalTerm
      base M j l i))

/-- The analogous termwise pullback-and-transport of the right chart
equation. -/
noncomputable def
    schemeModuleProjectiveSectionOverlapRightTransportedUniversalSum
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (schemeModuleProjectiveSectionOverlapPulledModule base M j l).sections :=
  sumSections (fun i => SheafOfModules.sectionsMap
    (schemeModuleProjectiveSectionOverlapRightModuleIso base M j l).hom
    (schemeModuleProjectiveSectionOverlapRightIteratedUniversalTerm
      base M j l i))

/-- The transported finite sum from the left chart is exactly the explicit
left-normalized overlap equation. -/
theorem schemeModuleProjectiveSectionOverlapLeftTransportedUniversalSum_eq
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionOverlapLeftTransportedUniversalSum base M j l =
      schemeModuleProjectiveSectionOverlapLeftUniversalSection base M j l := by
  rw [schemeModuleProjectiveSectionOverlapLeftUniversalSection_eq_sumTerms]
  unfold schemeModuleProjectiveSectionOverlapLeftTransportedUniversalSum
  congr 1
  funext i
  exact schemeModuleProjectiveSectionOverlapLeft_universalTerm_transport
    base M j l i

/-- The transported finite sum from the right chart is exactly the explicit
right-normalized overlap equation. -/
theorem schemeModuleProjectiveSectionOverlapRightTransportedUniversalSum_eq
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionOverlapRightTransportedUniversalSum base M j l =
      schemeModuleProjectiveSectionOverlapRightUniversalSection base M j l := by
  rw [schemeModuleProjectiveSectionOverlapRightUniversalSection_eq_sumTerms]
  unfold schemeModuleProjectiveSectionOverlapRightTransportedUniversalSum
  congr 1
  funext i
  exact schemeModuleProjectiveSectionOverlapRight_universalTerm_transport
    base M j l i

/-- The original left chart universal section, pulled to the overlap and
transported to the direct overlap pullback module. -/
noncomputable def schemeModuleProjectiveSectionOverlapLeftRestrictedUniversalSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (schemeModuleProjectiveSectionOverlapPulledModule base M j l).sections :=
  SheafOfModules.sectionsMap
    (schemeModuleProjectiveSectionOverlapLeftModuleIso base M j l).hom
    (pullbackSection
      (schemeModuleProjectiveSectionOverlapAmbientToLeft base M j l)
      (schemeModuleProjectiveSectionChartPulledModule base M j)
      (isIso_pullbackUnitComparison _)
      (schemeModuleProjectiveSectionChartUniversalSection base M j))

/-- The original right chart universal section, pulled to the overlap and
transported to the direct overlap pullback module. -/
noncomputable def schemeModuleProjectiveSectionOverlapRightRestrictedUniversalSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    (schemeModuleProjectiveSectionOverlapPulledModule base M j l).sections :=
  SheafOfModules.sectionsMap
    (schemeModuleProjectiveSectionOverlapRightModuleIso base M j l).hom
    (pullbackSection
      (schemeModuleProjectiveSectionOverlapAmbientToRight base M j l)
      (schemeModuleProjectiveSectionChartPulledModule base M l)
      (isIso_pullbackUnitComparison _)
      (schemeModuleProjectiveSectionChartUniversalSection base M l))

/-- Pulling the complete left chart equation to the overlap gives the
explicit left-normalized common-overlap equation. -/
theorem schemeModuleProjectiveSectionOverlapLeftRestrictedUniversalSection_eq
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionOverlapLeftRestrictedUniversalSection base M j l =
      schemeModuleProjectiveSectionOverlapLeftUniversalSection base M j l := by
  unfold schemeModuleProjectiveSectionOverlapLeftRestrictedUniversalSection
  rw [schemeModuleProjectiveSectionChartUniversalSection_eq_sumTerms,
    pullbackSection_sumSections, sectionsMap_sumSections]
  exact schemeModuleProjectiveSectionOverlapLeftTransportedUniversalSum_eq
    base M j l

/-- Pulling the complete right chart equation to the overlap gives the
explicit right-normalized common-overlap equation. -/
theorem schemeModuleProjectiveSectionOverlapRightRestrictedUniversalSection_eq
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    schemeModuleProjectiveSectionOverlapRightRestrictedUniversalSection base M j l =
      schemeModuleProjectiveSectionOverlapRightUniversalSection base M j l := by
  unfold schemeModuleProjectiveSectionOverlapRightRestrictedUniversalSection
  rw [schemeModuleProjectiveSectionChartUniversalSection_eq_sumTerms,
    pullbackSection_sumSections, sectionsMap_sumSections]
  exact schemeModuleProjectiveSectionOverlapRightTransportedUniversalSum_eq
    base M j l

/-- On every projective chart overlap, the two normalized universal
sections differ by the explicit invertible transition scalar. -/
theorem schemeModuleProjectiveSectionOverlap_universalSection_commonScale
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    scaleSection
      (unitEndomorphismOfRegularFunction
        (schemeModuleProjectiveSectionOverlapUnit base M j l))
      (schemeModuleProjectiveSectionOverlapRightUniversalSection base M j l) =
        schemeModuleProjectiveSectionOverlapLeftUniversalSection base M j l := by
  unfold schemeModuleProjectiveSectionOverlapRightUniversalSection
    schemeModuleProjectiveSectionOverlapLeftUniversalSection
    parameterizedSchemeModuleSection
  rw [finiteLinearCombinationSections_commonScale]
  congr 1
  funext i
  exact (unitEndomorphismOfRegularFunction_mul
      (X := schemeModuleProjectiveSectionOverlapAmbient base M j l)
      (schemeModuleProjectiveSectionOverlapUnit base M j l)
      (schemeModuleProjectiveSectionOverlapRightCoefficient base M j l i)).symm.trans
    (congrArg
      (fun r => unitEndomorphismOfRegularFunction
        (X := schemeModuleProjectiveSectionOverlapAmbient base M j l) r)
      (schemeModuleProjectiveSectionOverlap_coefficient_relation base M j l i).symm)

/-- The scalar endomorphism relating the two normalized overlap sections is
an isomorphism. -/
theorem isIso_schemeModuleProjectiveSectionOverlapUnitCoefficient
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M))) :
    IsIso (unitEndomorphismOfRegularFunction
      (schemeModuleProjectiveSectionOverlapUnit base M j l)) :=
  isIso_unitEndomorphismOfRegularFunction_of_isUnit _
    (isUnit_schemeModuleProjectiveSectionOverlapUnit base M j l)

/-- In any free trivialization of the pulled-back module, the two normalized
universal overlap sections define the same ideal sheaf. -/
theorem schemeModuleProjectiveSectionOverlap_zeroIdeal_eq
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    (I₀ : Type u)
    (e : SheafOfModules.free
        (R := (schemeModuleProjectiveSectionOverlapAmbient base M j l).ringCatSheaf) I₀ ≅
      (Scheme.Modules.pullback
        (pullback.fst base
          (schemeModuleProjectiveSectionOverlapToBase base M j l))).obj M) :
    sectionZeroIdealOfFreeIso I₀ e
        (schemeModuleProjectiveSectionOverlapLeftUniversalSection base M j l) =
      sectionZeroIdealOfFreeIso I₀ e
        (schemeModuleProjectiveSectionOverlapRightUniversalSection base M j l) := by
  letI := isIso_schemeModuleProjectiveSectionOverlapUnitCoefficient base M j l
  rw [← schemeModuleProjectiveSectionOverlap_universalSection_commonScale
    base M j l]
  exact sectionZeroIdealOfFreeIso_scaleSection_eq_of_isIso I₀ e _ _

/-- On an affine free-trivializing overlap, the two normalized universal
sections define the same scheme-theoretic zero locus. -/
theorem schemeModuleProjectiveSectionOverlap_zeroSubscheme_eq
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (j l : Fin (Module.finrank K (SchemeModuleGlobalSectionsOver base M)))
    [IsAffine (schemeModuleProjectiveSectionOverlapAmbient base M j l)]
    (I₀ : Type u)
    (e : SheafOfModules.free
        (R := (schemeModuleProjectiveSectionOverlapAmbient base M j l).ringCatSheaf) I₀ ≅
      (Scheme.Modules.pullback
        (pullback.fst base
          (schemeModuleProjectiveSectionOverlapToBase base M j l))).obj M) :
    sectionZeroSubschemeOfFreeIso I₀ e
        (schemeModuleProjectiveSectionOverlapLeftUniversalSection base M j l) =
      sectionZeroSubschemeOfFreeIso I₀ e
        (schemeModuleProjectiveSectionOverlapRightUniversalSection base M j l) := by
  letI := isIso_schemeModuleProjectiveSectionOverlapUnitCoefficient base M j l
  rw [← schemeModuleProjectiveSectionOverlap_universalSection_commonScale
    base M j l]
  exact sectionZeroSubschemeOfFreeIso_scaleSection_eq_of_isIso I₀ e _ _

end

end PfaffianDescent
