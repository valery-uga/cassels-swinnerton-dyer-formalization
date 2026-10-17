import PfaffianDescent.VoisinFixedLinearSystemEvaluation
import PfaffianDescent.VoisinFixedLinearSystemParameters

/-!
# Incidence for a universal family of divisors

A universal divisor of a projective section system is a closed subscheme of
`W ×ₛ T`, where `W` is the surface and `T` is the projective space of
sections.  This file specializes the presentation-independent incidence API
to that product.  It packages the map sending a configuration and a common
section parameter to each marked surface point paired with that parameter,
and gives the generic-avoidance theorem in the exact form used by Voisin.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- Pair the `i`th marked surface point with the common section parameter. -/
noncomputable def fixedLinearSystemIncidenceMap
    {S X W T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ S) (wBase : W ⟶ S) (tBase : T ⟶ S)
    (marked : ι → (X ⟶ W))
    (hmarked : ∀ i, marked i ≫ wBase = xBase) (i : ι) :
    properFiniteIncidenceParameterSpace xBase tBase ⟶
      pullback wBase tBase :=
  pullback.lift
    (pullback.fst xBase tBase ≫ marked i)
    (pullback.snd xBase tBase)
      (by
      calc
        (pullback.fst xBase tBase ≫ marked i) ≫ wBase =
            pullback.fst xBase tBase ≫ (marked i ≫ wBase) :=
          Category.assoc _ _ _
        _ = pullback.fst xBase tBase ≫ xBase := by rw [hmarked i]
        _ = pullback.snd xBase tBase ≫ tBase := pullback.condition)

@[reassoc]
theorem fixedLinearSystemIncidenceMap_fst
    {S X W T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ S) (wBase : W ⟶ S) (tBase : T ⟶ S)
    (marked : ι → (X ⟶ W))
    (hmarked : ∀ i, marked i ≫ wBase = xBase) (i : ι) :
    fixedLinearSystemIncidenceMap xBase wBase tBase marked hmarked i ≫
        pullback.fst wBase tBase =
      pullback.fst xBase tBase ≫ marked i := by
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem fixedLinearSystemIncidenceMap_snd
    {S X W T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ S) (wBase : W ⟶ S) (tBase : T ⟶ S)
    (marked : ι → (X ⟶ W))
    (hmarked : ∀ i, marked i ≫ wBase = xBase) (i : ι) :
    fixedLinearSystemIncidenceMap xBase wBase tBase marked hmarked i ≫
        pullback.snd wBase tBase =
      pullback.snd xBase tBase := by
  exact pullback.lift_snd _ _ _

/-- Configurations for which one member of the section family contains every
marked point. -/
noncomputable def fixedLinearSystemBadLocus
    {S X W T Z : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ S) (wBase : W ⟶ S) (tBase : T ⟶ S)
    (marked : ι → (X ⟶ W))
    (hmarked : ∀ i, marked i ≫ wBase = xBase)
    (zeroFamily : Z ⟶ pullback wBase tBase) : Set X :=
  properFiniteIncidenceBadLocus xBase tBase
    (fixedLinearSystemIncidenceMap xBase wBase tBase marked hmarked)
    (Set.range zeroFamily)

/-- A closed universal zero family and a proper section parameter space give
a closed simultaneous-divisor incidence locus. -/
theorem isClosed_fixedLinearSystemBadLocus
    {S X W T Z : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ S) (wBase : W ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (marked : ι → (X ⟶ W))
    (hmarked : ∀ i, marked i ≫ wBase = xBase)
    (zeroFamily : Z ⟶ pullback wBase tBase)
    [IsClosedImmersion zeroFamily] :
    IsClosed (fixedLinearSystemBadLocus
      xBase wBase tBase marked hmarked zeroFamily) :=
  isClosed_properFiniteIncidenceBadLocus_of_closedImmersion
    xBase tBase
      (fixedLinearSystemIncidenceMap xBase wBase tBase marked hmarked) zeroFamily

/-- A common parameter together with lifts of all marked point-parameter
pairs to the universal zero scheme puts the configuration in the bad locus. -/
theorem mem_fixedLinearSystemBadLocus_of_parameter
    {S X W T Z : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ S) (wBase : W ⟶ S) (tBase : T ⟶ S)
    (marked : ι → (X ⟶ W))
    (hmarked : ∀ i, marked i ≫ wBase = xBase)
    (zeroFamily : Z ⟶ pullback wBase tBase)
    (z : properFiniteIncidenceParameterSpace xBase tBase)
    (lift : ι → Z)
    (hlift : ∀ i, zeroFamily (lift i) =
      fixedLinearSystemIncidenceMap xBase wBase tBase marked hmarked i z) :
    pullback.fst xBase tBase z ∈
      fixedLinearSystemBadLocus
        xBase wBase tBase marked hmarked zeroFamily := by
  apply mem_properFiniteIncidenceBadLocus_of_parameter
    xBase tBase
      (fixedLinearSystemIncidenceMap xBase wBase tBase marked hmarked)
      (Set.range zeroFamily) z
  intro i
  exact ⟨lift i, hlift i⟩

/-- Generic avoidance for a universal divisor family, derived from faithful
evaluation and the numerical bound on its global-section space. -/
theorem genericFunctionField_avoids_fixedLinearSystem_of_evaluation_injective
    {K P V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Infinite P]
    {S X W T Z : Scheme.{u}} [IsIntegral X]
    (xBase : X ⟶ S) (wBase : W ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (n : ℕ) (marked : Fin n → (X ⟶ W))
    (hmarked : ∀ i, marked i ≫ wBase = xBase)
    (zeroFamily : Z ⟶ pullback wBase tBase) [IsClosedImmersion zeroFamily]
    (evaluation : V →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K V ≤ n)
    (configuration : (Fin n ↪ P) → X)
    (hbad : ∀ e : Fin n ↪ P,
      configuration e ∈ fixedLinearSystemBadLocus
        xBase wBase tBase marked hmarked zeroFamily →
      ∃ v : V, v ≠ 0 ∧ ∀ i, evaluation v (e i) = 0) :
    X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField) ∉
      fixedLinearSystemBadLocus
        xBase wBase tBase marked hmarked zeroFamily := by
  exact
    genericFunctionField_avoids_properFiniteIncidenceRange_of_evaluation_injective
      xBase tBase n
      (fixedLinearSystemIncidenceMap xBase wBase tBase marked hmarked)
      zeroFamily evaluation hevaluation hrank configuration hbad

/-- The preceding theorem for the literal global sections of a scheme
module. -/
theorem schemeModuleGlobalSections_generic_avoids_fixedLinearSystem
    {K P : Type u} [Field K] [Infinite P]
    {A S X W T Z : Scheme.{u}} [IsIntegral X]
    (base : A ⟶ Spec (.of K)) (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (xBase : X ⟶ S) (wBase : W ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (n : ℕ) (marked : Fin n → (X ⟶ W))
    (hmarked : ∀ i, marked i ≫ wBase = xBase)
    (zeroFamily : Z ⟶ pullback wBase tBase) [IsClosedImmersion zeroFamily]
    (evaluation : SchemeModuleGlobalSectionsOver base M →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K (SchemeModuleGlobalSectionsOver base M) ≤ n)
    (configuration : (Fin n ↪ P) → X)
    (hbad : ∀ e : Fin n ↪ P,
      configuration e ∈ fixedLinearSystemBadLocus
        xBase wBase tBase marked hmarked zeroFamily →
      ∃ s : SchemeModuleGlobalSectionsOver base M,
        s ≠ 0 ∧ ∀ i, evaluation s (e i) = 0) :
    X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField) ∉
      fixedLinearSystemBadLocus
        xBase wBase tBase marked hmarked zeroFamily :=
  genericFunctionField_avoids_fixedLinearSystem_of_evaluation_injective
    xBase wBase tBase n marked hmarked zeroFamily evaluation hevaluation
      hrank configuration hbad

/-- Scalar-extension-safe form for the universal divisor family.  An
offending projective parameter may have an arbitrary residue field; the
incidence-to-vanishing argument only has to show that this would destroy
injectivity of the basis-evaluation matrix over that field. -/
theorem
    schemeModuleGlobalSections_generic_avoids_fixedLinearSystem_after_fieldExtension
    {K P : Type u} [Field K] [Infinite P]
    {A S X W T Z : Scheme.{u}} [IsIntegral X]
    (base : A ⟶ Spec (.of K)) (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (xBase : X ⟶ S) (wBase : W ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (n : ℕ) (marked : Fin n → (X ⟶ W))
    (hmarked : ∀ i, marked i ≫ wBase = xBase)
    (zeroFamily : Z ⟶ pullback wBase tBase) [IsClosedImmersion zeroFamily]
    (evaluation : SchemeModuleGlobalSectionsOver base M →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K (SchemeModuleGlobalSectionsOver base M) ≤ n)
    (configuration : (Fin n ↪ P) → X)
    (hbad : ∀ e : Fin n ↪ P,
      configuration e ∈ fixedLinearSystemBadLocus
        xBase wBase tBase marked hmarked zeroFamily →
      ¬ ∀ {L : Type u} [Field L] (g : K →+* L),
        Function.Injective
          (fun c : Fin (Module.finrank K
              (SchemeModuleGlobalSectionsOver base M)) → L => fun i =>
            ∑ j, g (evaluation
              (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) j)
              (e i)) * c j)) :
    X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField) ∉
      fixedLinearSystemBadLocus
        xBase wBase tBase marked hmarked zeroFamily :=
  genericFunctionField_avoids_properFiniteIncidenceRange_of_scalarExtension_evaluation
    xBase tBase n
      (fixedLinearSystemIncidenceMap xBase wBase tBase marked hmarked)
      zeroFamily evaluation hevaluation hrank configuration hbad

/-- Witness form of scalar-extension-safe generic avoidance.  The geometric
incidence argument may exhibit an explicit field extension and a nonzero
kernel vector, instead of proving the logically equivalent failure of every
field-extension injectivity assertion directly. -/
theorem
    schemeModuleGlobalSections_generic_avoids_fixedLinearSystem_of_kernelWitness
    {K P : Type u} [Field K] [Infinite P]
    {A S X W T Z : Scheme.{u}} [IsIntegral X]
    (base : A ⟶ Spec (.of K)) (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (xBase : X ⟶ S) (wBase : W ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (n : ℕ) (marked : Fin n → (X ⟶ W))
    (hmarked : ∀ i, marked i ≫ wBase = xBase)
    (zeroFamily : Z ⟶ pullback wBase tBase) [IsClosedImmersion zeroFamily]
    (evaluation : SchemeModuleGlobalSectionsOver base M →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K (SchemeModuleGlobalSectionsOver base M) ≤ n)
    (configuration : (Fin n ↪ P) → X)
    (hkernel : ∀ e : Fin n ↪ P,
      configuration e ∈ fixedLinearSystemBadLocus
        xBase wBase tBase marked hmarked zeroFamily →
      ∃ (L : Type u) (_ : Field L) (g : K →+* L)
        (c : Fin (Module.finrank K
          (SchemeModuleGlobalSectionsOver base M)) → L),
        c ≠ 0 ∧
        (fun i => ∑ j, g (evaluation
          (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) j)
          (e i)) * c j) = 0) :
    X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField) ∉
      fixedLinearSystemBadLocus
        xBase wBase tBase marked hmarked zeroFamily := by
  apply schemeModuleGlobalSections_generic_avoids_fixedLinearSystem_after_fieldExtension
    base M xBase wBase tBase n marked hmarked zeroFamily evaluation
      hevaluation hrank configuration
  intro e hmem hall
  obtain ⟨L, hL, g, c, hc, hzero⟩ := hkernel e hmem
  letI : Field L := hL
  apply hc
  apply hall g
  funext i
  have hi := congrFun hzero i
  simpa using hi

/-- The generic configuration avoids the incidence loci for an entire
indexed collection of ground-field divisor systems.  The good configuration
may depend on the system; the generic point lies outside every proper closed
locus individually.  In particular, this step itself needs no countability
assumption on the index of Picard classes. -/
theorem genericFunctionField_avoids_all_fixedLinearSystems_of_goodConfigurations
    {S X W : Scheme.{u}} [IsIntegral X]
    {ι Class : Type}
    (xBase : X ⟶ S) (wBase : W ⟶ S)
    (marked : ι → (X ⟶ W))
    (hmarked : ∀ i, marked i ≫ wBase = xBase)
    (T Z : Class → Scheme.{u})
    (tBase : ∀ c, T c ⟶ S)
    (zeroFamily : ∀ c, Z c ⟶ pullback wBase (tBase c))
    (hproper : ∀ c, IsProper (tBase c))
    (hclosed : ∀ c, IsClosedImmersion (zeroFamily c))
    (hgood : ∀ c, ∃ x : X,
      x ∉ fixedLinearSystemBadLocus
        xBase wBase (tBase c) marked hmarked (zeroFamily c)) :
    X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField) ∉
      ⋃ c, fixedLinearSystemBadLocus
        xBase wBase (tBase c) marked hmarked (zeroFamily c) := by
  intro hmem
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hmem
  letI : IsProper (tBase c) := hproper c
  letI : IsClosedImmersion (zeroFamily c) := hclosed c
  have havoid := genericFunctionField_closedPoint_avoids_properFiniteIncidenceRange_of_exists
    xBase (tBase c)
    (fixedLinearSystemIncidenceMap xBase wBase (tBase c) marked hmarked)
    (zeroFamily c) (hgood c)
  exact havoid hc

/-- A family of fixed section systems, each detected injectively by a
configuration of at most `n` points, is avoided by the generic point all at
once, class by class.  The system may be indexed by an arbitrary type (for
example, the Picard group); no countability assumption is used. -/
theorem genericFunctionField_avoids_all_fixedLinearSystems_of_evaluation_injective
    {K P : Type u} [Field K] [Infinite P] {Class : Type}
    {S X W : Scheme.{u}} [IsIntegral X]
    {n : ℕ}
    (xBase : X ⟶ S) (wBase : W ⟶ S)
    (marked : Fin n → (X ⟶ W))
    (hmarked : ∀ i, marked i ≫ wBase = xBase)
    (T Z : Class → Scheme.{u})
    (tBase : ∀ c, T c ⟶ S)
    (zeroFamily : ∀ c, Z c ⟶ pullback wBase (tBase c))
    (hproper : ∀ c, IsProper (tBase c))
    (hclosed : ∀ c, IsClosedImmersion (zeroFamily c))
    (V : Class → Type u)
    [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]
    [∀ c, FiniteDimensional K (V c)]
    (evaluation : ∀ c, V c →ₗ[K] (P → K))
    (hevaluation : ∀ c, Function.Injective (evaluation c))
    (hrank : ∀ c, Module.finrank K (V c) ≤ n)
    (configuration : (Fin n ↪ P) → X)
    (hbad : ∀ c (e : Fin n ↪ P),
      configuration e ∈ fixedLinearSystemBadLocus
        xBase wBase (tBase c) marked hmarked (zeroFamily c) →
      ∃ v : V c, v ≠ 0 ∧ ∀ i, evaluation c v (e i) = 0) :
    X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField) ∉
      ⋃ c, fixedLinearSystemBadLocus
        xBase wBase (tBase c) marked hmarked (zeroFamily c) := by
  intro hmem
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hmem
  letI : IsProper (tBase c) := hproper c
  letI : IsClosedImmersion (zeroFamily c) := hclosed c
  have havoid := genericFunctionField_avoids_fixedLinearSystem_of_evaluation_injective
    xBase wBase (tBase c) n marked hmarked
    (zeroFamily c) (evaluation c) (hevaluation c) (hrank c)
    configuration (hbad c)
  exact havoid hc

end PfaffianDescent
