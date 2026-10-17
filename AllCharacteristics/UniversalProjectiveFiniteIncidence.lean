import AllCharacteristics.UniversalProjectiveIncidenceGeneric
import AllCharacteristics.UniversalProjectiveEquationFiber

/-!
# Finite universal projective incidence conditions

Voisin's generic-configuration argument excludes the existence of one
equation in a projective system that vanishes at every point of a finite
configuration.  This file supplies the general topological mechanism: impose
one universal incidence condition for each marked point, intersect those
closed conditions on a proper parameter family, and project to the base.
The resulting bad locus is closed, so an integral base's generic point avoids
it whenever a single good parameter value exists.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

namespace AllCharacteristics
namespace UniversalHomogeneous

open HomogeneousProjective

universe u

variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The parameter space obtained by adjoining a proper family of projective
equations to a base over `Spec R`. -/
noncomputable abbrev projectiveUniversalFiniteIncidenceParameterSpace
    {X T : Scheme.{u}}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R)) : Scheme.{u} :=
  pullback xBase tBase

/-- The projection from the equation-parameter space to the configuration
base. -/
noncomputable abbrev projectiveUniversalFiniteIncidenceParameterProjection
    {X T : Scheme.{u}}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R)) :
    projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase ⟶ X :=
  pullback.fst xBase tBase

/-- The universal incidence parameter map for one marked ambient point and
one equation in the proper parameter family. -/
noncomputable def projectiveUniversalFiniteIncidenceParameterMap
    {X T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d) (i : ι) :
    projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase ⟶
      Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯ projectiveParameters R σ d :=
  Limits.prod.lift
    (pullback.fst xBase tBase ≫ a i)
    (pullback.snd xBase tBase ≫ s)

/-- The ambient projection of a finite-incidence parameter map is the
specified marked ambient point. -/
theorem projectiveUniversalFiniteIncidenceParameterMap_fst
    {X T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d) (i : ι) :
    projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i ≫
      Limits.prod.fst = pullback.fst xBase tBase ≫ a i :=
  Limits.prod.lift_fst _ _

/-- The coefficient projection of a finite-incidence parameter map is its
selected equation parameter. -/
theorem projectiveUniversalFiniteIncidenceParameterMap_snd
    {X T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d) (i : ι) :
    projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i ≫
      Limits.prod.snd = pullback.snd xBase tBase ≫ s :=
  Limits.prod.lift_snd _ _

/-- The base locus where one equation from the proper parameter family
vanishes at every marked ambient point. -/
noncomputable def projectiveUniversalFiniteIncidenceBadLocus
    {X T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d) : Set X :=
  (projectiveUniversalFiniteIncidenceParameterProjection R xBase tBase) ''
    ⋂ i, (projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i) ⁻¹'
      Set.range (projectiveUniversalIncidence R σ d)

/-- Membership in the finite-incidence bad locus supplies one equation
parameter over the configuration and a universal-incidence witness at every
marked ambient point. -/
theorem exists_parameter_of_mem_projectiveUniversalFiniteIncidenceBadLocus
    {X T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d)
    {x : X}
    (hx : x ∈ projectiveUniversalFiniteIncidenceBadLocus R σ d xBase tBase a s) :
    ∃ z : projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase,
      projectiveUniversalFiniteIncidenceParameterProjection R xBase tBase z = x ∧
        ∀ i : ι,
          projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i z ∈
            Set.range (projectiveUniversalIncidence R σ d) := by
  obtain ⟨z, hz, hzx⟩ := hx
  refine ⟨z, hzx, ?_⟩
  intro i
  exact Set.mem_iInter.mp hz i

/-- Conversely, a field-valued equation parameter with simultaneous
universal-incidence lifts at all marked points puts the resulting
configuration point in the finite-incidence bad locus.  Together with
`exists_parameter_of_mem_projectiveUniversalFiniteIncidenceBadLocus`, this
identifies the carrier-level bad locus with the usual statement that one
projective equation vanishes at all marked points. -/
theorem mem_projectiveUniversalFiniteIncidenceBadLocus_of_common_fieldPoints
    {X T : Scheme.{u}} {n : ℕ}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (a : Fin n → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d)
    {L : Type u} [Field L]
    (r : Spec (.of L) ⟶ X) (t : Spec (.of L) ⟶ T)
    (hbase : r ≫ xBase = t ≫ tBase)
    (q : Fin n → (Spec (.of L) ⟶ projectiveUniversalFamily R σ d))
    (hq : ∀ i, q i ≫ projectiveUniversalIncidence R σ d =
      pullback.lift r t hbase ≫
        projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i) :
    r (IsLocalRing.closedPoint L) ∈
      projectiveUniversalFiniteIncidenceBadLocus R σ d xBase tBase a s := by
  let z : projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase :=
    pullback.lift r t hbase (IsLocalRing.closedPoint L)
  refine ⟨z, ?_, ?_⟩
  · apply Set.mem_iInter.mpr
    intro i
    refine ⟨q i (IsLocalRing.closedPoint L), ?_⟩
    exact congrArg (fun f => f (IsLocalRing.closedPoint L)) (hq i)
  · change pullback.fst xBase tBase
      (pullback.lift r t hbase (IsLocalRing.closedPoint L)) = _
    exact congrArg (fun f => f (IsLocalRing.closedPoint L))
      (pullback.lift_fst r t hbase)

/-- A carrier point outside the finite-incidence bad locus has no nonzero
projective equation parameter, even after passing canonically to its residue
field, with incidence lifts through all marked points.  This is the
pointwise converse form used to read avoidance as injectivity of evaluation. -/
theorem not_exists_common_residueFieldPoints_of_not_mem_projectiveUniversalFiniteIncidenceBadLocus
    {X T : Scheme.{u}} {n : ℕ}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (a : Fin n → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d)
    {x : X}
    (hx : x ∉ projectiveUniversalFiniteIncidenceBadLocus R σ d xBase tBase a s) :
    ¬ ∃ (t : Spec (.of (X.residueField x)) ⟶ T)
      (q : Fin n → (Spec (.of (X.residueField x)) ⟶
        projectiveUniversalFamily R σ d))
      (hbase : X.fromSpecResidueField x ≫ xBase = t ≫ tBase),
      ∀ i, q i ≫ projectiveUniversalIncidence R σ d =
        pullback.lift (X.fromSpecResidueField x) t hbase ≫
          projectiveUniversalFiniteIncidenceParameterMap R σ d
            xBase tBase a s i := by
  rintro ⟨t, q, hbase, hq⟩
  apply hx
  have hmem := mem_projectiveUniversalFiniteIncidenceBadLocus_of_common_fieldPoints
    R σ d xBase tBase a s (X.fromSpecResidueField x) t hbase q hq
  have heq :
      (X.fromSpecResidueField x)
        (IsLocalRing.closedPoint
          (IsLocalRing.ResidueField (X.presheaf.stalk x))) = x := by
    apply Scheme.fromSpecResidueField_apply
  exact heq ▸ hmem

/-- A point in the carrier image of an arbitrary scheme morphism lifts to a
field-valued point of that morphism after a residue-field extension.  The
lifted point of the source has exactly the prescribed singleton carrier
image. -/
theorem exists_fieldPoint_of_mem_range
    {B U Y : Scheme.{u}} (b : B ⟶ Y) (f : U ⟶ Y) (z : B)
    (hz : b z ∈ Set.range f) :
    ∃ (L : Type u) (_ : Field L) (r : Spec (.of L) ⟶ B)
      (q : Spec (.of L) ⟶ U),
      Set.range r = {z} ∧ q ≫ f = r ≫ b := by
  have hz' : z ∈ Set.range (pullback.fst b f) := by
    rw [AlgebraicGeometry.Scheme.Pullback.range_fst]
    exact hz
  obtain ⟨w, hw⟩ := hz'
  let L : Type u := (pullback b f).residueField w
  let r : Spec (.of L) ⟶ B :=
    (pullback b f).fromSpecResidueField w ≫ pullback.fst b f
  let q : Spec (.of L) ⟶ U :=
    (pullback b f).fromSpecResidueField w ≫ pullback.snd b f
  refine ⟨L, inferInstance, r, q, ?_, ?_⟩
  · dsimp only [r]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.range_fromSpecResidueField, Set.image_singleton, hw]
  · change ((pullback b f).fromSpecResidueField w ≫ pullback.snd b f) ≫ f =
      ((pullback b f).fromSpecResidueField w ≫ pullback.fst b f) ≫ b
    rw [Category.assoc, Category.assoc, pullback.condition]

/-- Finitely many carrier-level lifts through one morphism can be realized
over a single field.  The construction successively extends the residue
field, transporting the earlier field-valued lifts at every step. -/
theorem exists_common_fieldPoint_of_mem_range_fin
    {B U Y : Scheme.{u}} (f : U ⟶ Y) :
    ∀ (n : ℕ) (b : Fin n → (B ⟶ Y)) (z : B),
      (∀ i, b i z ∈ Set.range f) →
      ∃ (L : Type u) (_ : Field L) (r : Spec (.of L) ⟶ B)
        (q : Fin n → (Spec (.of L) ⟶ U)),
        Set.range r = {z} ∧ ∀ i, q i ≫ f = r ≫ b i := by
  intro n
  induction n with
  | zero =>
      intro b z hz
      refine ⟨B.residueField z, inferInstance, B.fromSpecResidueField z,
        fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · exact B.range_fromSpecResidueField z
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      intro b z hz
      obtain ⟨L, hL, r, q, hrange, hq⟩ :=
        ih (fun i ↦ b i.succ) z (fun i ↦ hz i.succ)
      letI : Field L := hL
      let cL : Spec (.of L) := IsLocalRing.closedPoint L
      have hrpoint : r cL = z := by
        have hmem : r cL ∈ Set.range r := ⟨cL, rfl⟩
        rw [hrange] at hmem
        simpa only [Set.mem_singleton_iff] using hmem
      have hmem : (r ≫ b 0) cL ∈ Set.range f := by
        change b 0 (r cL) ∈ Set.range f
        rw [hrpoint]
        exact hz 0
      obtain ⟨E, hE, s, t, hsrange, ht⟩ :=
        exists_fieldPoint_of_mem_range (r ≫ b 0) f cL hmem
      letI : Field E := hE
      refine ⟨E, hE, s ≫ r, Fin.cases t (fun i ↦ s ≫ q i), ?_, ?_⟩
      · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
          hsrange, Set.image_singleton, hrpoint]
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simpa only [Fin.cases_zero, Category.assoc] using ht
        · have hqj := hq j
          calc
            (s ≫ q j) ≫ f = s ≫ (q j ≫ f) := Category.assoc _ _ _
            _ = s ≫ (r ≫ b j.succ) := by rw [hqj]
            _ = (s ≫ r) ≫ b j.succ := (Category.assoc _ _ _).symm

/-- All marked universal-incidence memberships of a finite configuration can
be lifted over one field and one parameter point.  Every lifted universal
family point is therefore attached to the same equation parameter. -/
theorem exists_common_fieldPoint_of_mem_all_parameterMap_range
    {X T : Scheme.{u}} {n : ℕ}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (a : Fin n → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d)
    (z : projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase)
    (hz : ∀ i : Fin n,
      projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i z ∈
        Set.range (projectiveUniversalIncidence R σ d)) :
    ∃ (L : Type u) (_ : Field L)
      (r : Spec (.of L) ⟶ projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase)
      (q : Fin n → (Spec (.of L) ⟶ projectiveUniversalFamily R σ d)),
      Set.range r = {z} ∧ ∀ i,
        q i ≫ projectiveUniversalIncidence R σ d =
          r ≫ projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i := by
  exact exists_common_fieldPoint_of_mem_range_fin (projectiveUniversalIncidence R σ d) n
    (fun i ↦ projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i) z hz

/-- All marked universal-incidence memberships of a finite configuration can
be represented in one normalized coefficient chart over one field.  The
specialized equation and all of its marked ambient roots therefore share one
coefficient homomorphism. -/
theorem exists_common_normalizedForm_fieldPoints_of_mem_all_parameterMap_range
    {X T : Scheme.{u}} {n : ℕ}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (a : Fin n → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d)
    (z : projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase)
    (hz : ∀ i : Fin n,
      projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i z ∈
        Set.range (projectiveUniversalIncidence R σ d)) :
    ∃ (L : Type u) (_ : Field L)
      (r : Spec (.of L) ⟶ projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase)
      (j : Monomials σ d)
      (u : Spec (.of L) ⟶ Spec (.of (ParameterChartRing R σ d j)))
      (qj : Fin n → (Spec (.of L) ⟶ hypersurface (normalizedForm R σ d j)
        (normalizedForm_isHomogeneous R σ d j))),
      Set.range r = {z} ∧
        u ≫ parameterChartι R σ d j = r ≫ pullback.snd xBase tBase ≫ s ∧
        (∀ i, qj i ≫ normalizedFamilyToAmbient R σ d j =
          r ≫ pullback.fst xBase tBase ≫ a i) ∧
        ∀ i, qj i ≫ normalizedFamilyToBase R σ d j = u := by
  obtain ⟨L, hL, r, q, hrange, hq⟩ :=
    exists_common_fieldPoint_of_mem_all_parameterMap_range R σ d xBase tBase a s z hz
  letI : Field L := hL
  have hbase : ∀ i, q i ≫ projectiveUniversalToBase R σ d =
      r ≫ pullback.snd xBase tBase ≫ s := by
    intro i
    calc
      q i ≫ projectiveUniversalToBase R σ d =
          q i ≫ projectiveUniversalIncidence R σ d ≫ Limits.prod.snd := by
            exact (congrArg (fun f ↦ q i ≫ f)
              (projectiveUniversalIncidence_snd R σ d)).symm
      _ = r ≫ projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i ≫
          Limits.prod.snd := by
            simpa only [Category.assoc] using
              congrArg (fun f ↦ f ≫ Limits.prod.snd) (hq i)
      _ = r ≫ pullback.snd xBase tBase ≫ s := by
            exact congrArg (fun f ↦ r ≫ f)
              (projectiveUniversalFiniteIncidenceParameterMap_snd R σ d xBase tBase a s i)
  obtain ⟨j, u, qj, hu, hqj, hbaseqj⟩ :=
    exists_normalizedForm_fieldPoints_of_common_base q
      (r ≫ pullback.snd xBase tBase ≫ s) hbase
  refine ⟨L, hL, r, j, u, qj, hrange, hu, ?_, hbaseqj⟩
  intro i
  calc
    qj i ≫ normalizedFamilyToAmbient R σ d j =
        qj i ≫ projectiveUniversalChartι R σ d j ≫
          projectiveUniversalToAmbient R σ d := by
            exact (congrArg (fun f ↦ qj i ≫ f)
              (projectiveUniversalChartι_toAmbient R σ d j)).symm
    _ = q i ≫ projectiveUniversalToAmbient R σ d := by
          simpa only [Category.assoc] using
            congrArg (fun f ↦ f ≫ projectiveUniversalToAmbient R σ d) (hqj i)
    _ = q i ≫ projectiveUniversalIncidence R σ d ≫ Limits.prod.fst := by
          exact (congrArg (fun f ↦ q i ≫ f)
            (projectiveUniversalIncidence_fst R σ d)).symm
    _ = r ≫ projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i ≫
        Limits.prod.fst := by
          simpa only [Category.assoc] using
            congrArg (fun f ↦ f ≫ Limits.prod.fst) (hq i)
    _ = r ≫ pullback.fst xBase tBase ≫ a i := by
          exact congrArg (fun f ↦ r ≫ f)
            (projectiveUniversalFiniteIncidenceParameterMap_fst R σ d xBase tBase a s i)

/-- A point in the finite-incidence locus lifts to a field-valued point of
the actual universal incidence pullback.  Unlike a statement only about
carrier points, this retains the equality of the two maps to the incidence
product after passing to the residue field. -/
theorem exists_fieldPoint_of_mem_parameterMap_range
    {X T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d)
    (z : projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase)
    (i : ι)
    (hz : projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i z ∈
      Set.range (projectiveUniversalIncidence R σ d)) :
    ∃ (L : Type u) (_ : Field L)
      (r : Spec (.of L) ⟶ projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase)
      (q : Spec (.of L) ⟶ projectiveUniversalFamily R σ d),
      Set.range r = {z} ∧
        q ≫ projectiveUniversalIncidence R σ d =
          r ≫ projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i := by
  let b := projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i
  have hz' : z ∈ Set.range
      (pullback.fst b (projectiveUniversalIncidence R σ d)) := by
    rw [AlgebraicGeometry.Scheme.Pullback.range_fst]
    exact hz
  obtain ⟨w, hw⟩ := hz'
  let L : Type u := (pullback b (projectiveUniversalIncidence R σ d)).residueField w
  let r : Spec (.of L) ⟶ projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase :=
    (pullback b (projectiveUniversalIncidence R σ d)).fromSpecResidueField w ≫
      pullback.fst b (projectiveUniversalIncidence R σ d)
  let q : Spec (.of L) ⟶ projectiveUniversalFamily R σ d :=
    (pullback b (projectiveUniversalIncidence R σ d)).fromSpecResidueField w ≫
      pullback.snd b (projectiveUniversalIncidence R σ d)
  refine ⟨L, inferInstance, r, q, ?_, ?_⟩
  · dsimp only [r]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.range_fromSpecResidueField, Set.image_singleton, hw]
  · change ((pullback b (projectiveUniversalIncidence R σ d)).fromSpecResidueField w ≫
        pullback.snd b (projectiveUniversalIncidence R σ d)) ≫
          projectiveUniversalIncidence R σ d =
        ((pullback b (projectiveUniversalIncidence R σ d)).fromSpecResidueField w ≫
          pullback.fst b (projectiveUniversalIncidence R σ d)) ≫ b
    rw [Category.assoc, Category.assoc, pullback.condition]

/-- A finite-incidence witness produces a normalized equation over one field
whose ambient point and coefficient parameter agree, as scheme morphisms,
with the selected marked point and parameter. -/
theorem exists_normalizedForm_fieldPoint_ambient_and_parameter_of_mem_parameterMap_range
    {X T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d)
    (z : projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase)
    (i : ι)
    (hz : projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i z ∈
      Set.range (projectiveUniversalIncidence R σ d)) :
    ∃ (L : Type u) (_ : Field L)
      (r : Spec (.of L) ⟶ projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase)
      (j : Monomials σ d)
      (q : Spec (.of L) ⟶ hypersurface (normalizedForm R σ d j)
        (normalizedForm_isHomogeneous R σ d j)),
      Set.range r = {z} ∧
        q ≫ normalizedFamilyToAmbient R σ d j =
          r ≫ pullback.fst xBase tBase ≫ a i ∧
        q ≫ normalizedFamilyToBase R σ d j ≫ parameterChartι R σ d j =
          r ≫ pullback.snd xBase tBase ≫ s := by
  obtain ⟨L, hL, r, q, hrange, hq⟩ :=
    exists_fieldPoint_of_mem_parameterMap_range R σ d xBase tBase a s z i hz
  letI : Field L := hL
  obtain ⟨j, qj, hqj⟩ := exists_normalizedForm_fieldPoint q
  refine ⟨L, hL, r, j, qj, hrange, ?_, ?_⟩
  · have hfst : q ≫ projectiveUniversalIncidence R σ d ≫ Limits.prod.fst =
      r ≫ projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i ≫
        Limits.prod.fst := by
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ Limits.prod.fst) hq
    calc
      qj ≫ normalizedFamilyToAmbient R σ d j =
          qj ≫ (projectiveUniversalChartι R σ d j ≫
            projectiveUniversalToAmbient R σ d) := by
            rw [projectiveUniversalChartι_toAmbient]
      _ = (qj ≫ projectiveUniversalChartι R σ d j) ≫
          projectiveUniversalToAmbient R σ d := (Category.assoc _ _ _).symm
      _ = q ≫ projectiveUniversalToAmbient R σ d := by rw [hqj]
      _ = q ≫ projectiveUniversalIncidence R σ d ≫ Limits.prod.fst := by
            rw [projectiveUniversalIncidence_fst]
      _ = r ≫ projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i ≫
          Limits.prod.fst := hfst
      _ = r ≫ pullback.fst xBase tBase ≫ a i := by
            rw [projectiveUniversalFiniteIncidenceParameterMap_fst]
  · have hsnd : q ≫ projectiveUniversalIncidence R σ d ≫ Limits.prod.snd =
      r ≫ projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i ≫
        Limits.prod.snd := by
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ Limits.prod.snd) hq
    calc
      qj ≫ normalizedFamilyToBase R σ d j ≫ parameterChartι R σ d j =
          qj ≫ (projectiveUniversalChartι R σ d j ≫
            projectiveUniversalToBase R σ d) := by
            rw [projectiveUniversalChartι_toBase]
      _ = (qj ≫ projectiveUniversalChartι R σ d j) ≫
          projectiveUniversalToBase R σ d := (Category.assoc _ _ _).symm
      _ = q ≫ projectiveUniversalToBase R σ d := by rw [hqj]
      _ = q ≫ projectiveUniversalIncidence R σ d ≫ Limits.prod.snd := by
            rw [projectiveUniversalIncidence_snd]
      _ = r ≫ projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i ≫
          Limits.prod.snd := hsnd
      _ = r ≫ pullback.snd xBase tBase ≫ s := by
            rw [projectiveUniversalFiniteIncidenceParameterMap_snd]

/-- An incidence witness for one member of a finite configuration can be
written in a normalized coefficient chart.  The chart point has exactly the
marked ambient point and the selected coefficient parameter of the original
finite-incidence parameter. -/
theorem exists_normalizedForm_residueField_coordinates_of_mem_parameterMap_range
    {X T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d)
    (z : projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase)
    (i : ι)
    (hz : projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i z ∈
      Set.range (projectiveUniversalIncidence R σ d)) :
    ∃ (j : Monomials σ d)
      (y : hypersurface (normalizedForm R σ d j)
        (normalizedForm_isHomogeneous R σ d j)),
      normalizedFamilyToAmbient R σ d j y =
        a i (pullback.fst xBase tBase z) ∧
      (normalizedFamilyToBase R σ d j ≫ parameterChartι R σ d j) y =
        (pullback.snd xBase tBase ≫ s) z ∧
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
  obtain ⟨j, y, hy, hv⟩ :=
    exists_normalizedForm_residueField_coordinates_of_mem_range hz
  refine ⟨j, y, ?_, ?_, hv⟩
  · have hfst := congrArg (fun w ↦ (Limits.prod.fst :
        Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯ projectiveParameters R σ d ⟶
          Proj (MvPolynomial.homogeneousSubmodule σ R)) w) hy
    calc
      normalizedFamilyToAmbient R σ d j y =
          (Limits.prod.fst : Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
            projectiveParameters R σ d ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
            (Limits.prod.lift (normalizedFamilyToAmbient R σ d j)
              (normalizedFamilyToBase R σ d j ≫ parameterChartι R σ d j) y) := by
            change _ = ((Limits.prod.lift (normalizedFamilyToAmbient R σ d j)
              (normalizedFamilyToBase R σ d j ≫ parameterChartι R σ d j) ≫
                Limits.prod.fst) y)
            rw [Limits.prod.lift_fst]
      _ = (Limits.prod.fst : Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
          projectiveParameters R σ d ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
          (Limits.prod.lift (pullback.fst xBase tBase ≫ a i)
            (pullback.snd xBase tBase ≫ s) z) := hfst
      _ = a i (pullback.fst xBase tBase z) := by
            change ((Limits.prod.lift (pullback.fst xBase tBase ≫ a i)
              (pullback.snd xBase tBase ≫ s) ≫ Limits.prod.fst) z) = _
            rw [Limits.prod.lift_fst, Scheme.Hom.comp_apply]
  · have hsnd := congrArg (fun w ↦ (Limits.prod.snd :
        Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯ projectiveParameters R σ d ⟶
          projectiveParameters R σ d) w) hy
    calc
      (normalizedFamilyToBase R σ d j ≫ parameterChartι R σ d j) y =
          (Limits.prod.snd : Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
            projectiveParameters R σ d ⟶ projectiveParameters R σ d)
            (Limits.prod.lift (normalizedFamilyToAmbient R σ d j)
              (normalizedFamilyToBase R σ d j ≫ parameterChartι R σ d j) y) := by
            change _ = ((Limits.prod.lift (normalizedFamilyToAmbient R σ d j)
              (normalizedFamilyToBase R σ d j ≫ parameterChartι R σ d j) ≫
                Limits.prod.snd) y)
            rw [Limits.prod.lift_snd]
      _ = (Limits.prod.snd : Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
          projectiveParameters R σ d ⟶ projectiveParameters R σ d)
          (Limits.prod.lift (pullback.fst xBase tBase ≫ a i)
            (pullback.snd xBase tBase ≫ s) z) := hsnd
      _ = (pullback.snd xBase tBase ≫ s) z := by
            change ((Limits.prod.lift (pullback.fst xBase tBase ≫ a i)
              (pullback.snd xBase tBase ≫ s) ≫ Limits.prod.snd) z) = _
            rw [Limits.prod.lift_snd, Scheme.Hom.comp_apply]

/-- The simultaneous finite-incidence bad locus is closed whenever the
equation parameter family is proper over the coefficient base. -/
theorem isClosed_projectiveUniversalFiniteIncidenceBadLocus
    {X T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R)) [IsProper tBase]
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d) :
    IsClosed (projectiveUniversalFiniteIncidenceBadLocus R σ d xBase tBase a s) := by
  let π := projectiveUniversalFiniteIncidenceParameterProjection R xBase tBase
  letI : IsProper π := by
    change IsProper (pullback.fst xBase tBase)
    infer_instance
  change IsClosed (π '' ⋂ i,
    (projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i) ⁻¹'
      Set.range (projectiveUniversalIncidence R σ d))
  apply π.isClosedMap
  apply isClosed_iInter
  intro i
  exact (isClosed_range_projectiveUniversalIncidence R σ d).preimage
    (projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i).continuous

/-- The generic function-field point of an integral base avoids any proper
finite-incidence bad locus. -/
theorem genericFunctionField_closedPoint_avoids_projectiveUniversalFiniteIncidence
    {X T : Scheme.{u}} {ι : Type} [IsIntegral X]
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R)) [IsProper tBase]
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d)
    (hproper : projectiveUniversalFiniteIncidenceBadLocus R σ d xBase tBase a s ≠
      Set.univ) :
    X.fromSpecStalk (genericPoint X) (IsLocalRing.closedPoint X.functionField) ∉
      projectiveUniversalFiniteIncidenceBadLocus R σ d xBase tBase a s :=
  genericFunctionField_closedPoint_avoids_proper_closed X
    (isClosed_projectiveUniversalFiniteIncidenceBadLocus R σ d xBase tBase a s) hproper

/-- A single configuration point outside the simultaneous-incidence image
proves that image proper, hence proves generic avoidance. -/
theorem genericFunctionField_closedPoint_avoids_projectiveUniversalFiniteIncidence_of_exists
    {X T : Scheme.{u}} {ι : Type} [IsIntegral X]
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R)) [IsProper tBase]
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d)
    (hgood : ∃ x : X,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus R σ d xBase tBase a s) :
    X.fromSpecStalk (genericPoint X) (IsLocalRing.closedPoint X.functionField) ∉
      projectiveUniversalFiniteIncidenceBadLocus R σ d xBase tBase a s := by
  apply genericFunctionField_closedPoint_avoids_projectiveUniversalFiniteIncidence
    R σ d xBase tBase a s
  intro hbad
  obtain ⟨x, hx⟩ := hgood
  apply hx
  rw [hbad]
  exact Set.mem_univ x

/-- At the generic point, the closed finite-incidence avoidance statement
rules out a common field-valued equation parameter and simultaneous
universal-family lifts at all marked points.  This is the direct form needed
to turn generic avoidance into injectivity of a restriction map once a
linear system has been parameterized. -/
theorem not_exists_common_fieldPoints_at_generic_of_exists
    {X T : Scheme.{u}} {n : ℕ} [IsIntegral X]
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R)) [IsProper tBase]
    (a : Fin n → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d)
    (hgood : ∃ x : X,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus R σ d xBase tBase a s) :
    ¬ ∃ (t : Spec (.of X.functionField) ⟶ T)
      (q : Fin n → (Spec (.of X.functionField) ⟶ projectiveUniversalFamily R σ d))
      (hbase : X.fromSpecStalk (genericPoint X) ≫ xBase = t ≫ tBase),
      ∀ i, q i ≫ projectiveUniversalIncidence R σ d =
        pullback.lift (X.fromSpecStalk (genericPoint X)) t hbase ≫
          projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i := by
  rintro ⟨t, q, hbase, hq⟩
  apply (genericFunctionField_closedPoint_avoids_projectiveUniversalFiniteIncidence_of_exists
    R σ d xBase tBase a s hgood)
  exact mem_projectiveUniversalFiniteIncidenceBadLocus_of_common_fieldPoints
    R σ d xBase tBase a s (X.fromSpecStalk (genericPoint X)) t hbase q hq

/-- A morphism of configuration bases carries a finite universal-incidence
bad locus forward whenever its marked ambient maps are the pullbacks of the
target marked maps.  Unlike the permutation result below, the source and
target configuration bases may be different schemes. -/
theorem mapsTo_projectiveUniversalFiniteIncidenceBadLocus_of_maps
    {X Y T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ Spec (.of R)) (yBase : Y ⟶ Spec (.of R))
    (tBase : T ⟶ Spec (.of R))
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (b : ι → (Y ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d)
    (u : X ⟶ Y) (hu : u ≫ yBase = xBase)
    (hab : ∀ i, u ≫ b i = a i) :
    Set.MapsTo u
      (projectiveUniversalFiniteIncidenceBadLocus R σ d xBase tBase a s)
      (projectiveUniversalFiniteIncidenceBadLocus R σ d yBase tBase b s) := by
  let v : projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase ⟶
      projectiveUniversalFiniteIncidenceParameterSpace R yBase tBase :=
    pullback.lift
      (pullback.fst xBase tBase ≫ u)
      (pullback.snd xBase tBase)
      (by rw [Category.assoc, hu, pullback.condition])
  have hvfst : v ≫ pullback.fst yBase tBase = pullback.fst xBase tBase ≫ u := by
    exact pullback.lift_fst _ _ _
  have hvsnd : v ≫ pullback.snd yBase tBase = pullback.snd xBase tBase := by
    exact pullback.lift_snd _ _ _
  have hvparameter (i : ι) : v ≫
      projectiveUniversalFiniteIncidenceParameterMap R σ d yBase tBase b s i =
        projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i := by
    apply Limits.prod.hom_ext
    · simp only [Category.assoc, projectiveUniversalFiniteIncidenceParameterMap,
        Limits.prod.lift_fst]
      rw [← Category.assoc, hvfst, Category.assoc, hab]
    · simp only [Category.assoc, projectiveUniversalFiniteIncidenceParameterMap,
        Limits.prod.lift_snd]
      rw [← Category.assoc, hvsnd]
  have hvprojection : v ≫
      projectiveUniversalFiniteIncidenceParameterProjection R yBase tBase =
        projectiveUniversalFiniteIncidenceParameterProjection R xBase tBase ≫ u := by
    exact hvfst
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hx
  refine ⟨v z, ?_, ?_⟩
  · apply Set.mem_iInter.mpr
    intro i
    have hi := Set.mem_iInter.mp hz i
    change (projectiveUniversalFiniteIncidenceParameterMap R σ d yBase tBase b s i)
      (v z) ∈ Set.range (projectiveUniversalIncidence R σ d)
    change (v ≫ projectiveUniversalFiniteIncidenceParameterMap R σ d yBase tBase b s i)
      z ∈ Set.range (projectiveUniversalIncidence R σ d)
    rw [hvparameter i]
    exact hi
  · change (projectiveUniversalFiniteIncidenceParameterProjection R yBase tBase) (v z) = u x
    change (v ≫ projectiveUniversalFiniteIncidenceParameterProjection R yBase tBase) z = u x
    rw [hvprojection]
    exact congrArg u hzx

/-- A generic configuration avoids the finite-incidence bad locus for every
member of an indexed family of proper projective equation systems, provided
each system has one good configuration.  The parameter schemes may vary with
the index.  This is the finite-incidence form needed to treat the separate
linear systems attached to the Picard classes in Voisin's argument. -/
theorem genericFunctionField_closedPoint_avoids_projectiveUniversalFiniteIncidence_family_of_exists
    {X : Scheme.{u}} {ι : Type} [IsIntegral X] {κ : Sort v}
    (xBase : X ⟶ Spec (.of R)) (T : κ → Scheme.{u})
    (tBase : ∀ c, T c ⟶ Spec (.of R))
    (hproperT : ∀ c, IsProper (tBase c))
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : ∀ c, T c ⟶ projectiveParameters R σ d)
    (hgood : ∀ c, ∃ x : X,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus R σ d xBase (tBase c) a (s c)) :
    ∀ c, X.fromSpecStalk (genericPoint X)
      (IsLocalRing.closedPoint X.functionField) ∉
      projectiveUniversalFiniteIncidenceBadLocus R σ d xBase (tBase c) a (s c) := by
  intro c
  letI : IsProper (tBase c) := hproperT c
  exact genericFunctionField_closedPoint_avoids_projectiveUniversalFiniteIncidence_of_exists
    R σ d xBase (tBase c) a (s c) (hgood c)

/-- Reindex a finite-incidence parameter space by an endomorphism of the
configuration base which is over the coefficient base. -/
noncomputable def projectiveUniversalFiniteIncidenceParameterReindex
    {X T : Scheme.{u}}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (u : X ⟶ X) (hu : u ≫ xBase = xBase) :
    projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase ⟶
      projectiveUniversalFiniteIncidenceParameterSpace R xBase tBase :=
  pullback.lift
    (pullback.fst xBase tBase ≫ u)
    (pullback.snd xBase tBase)
    (by rw [Category.assoc, hu, pullback.condition])

/-- Reindexing changes the configuration coordinate of the parameter space
by the given base endomorphism. -/
theorem projectiveUniversalFiniteIncidenceParameterReindex_fst
    {X T : Scheme.{u}}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (u : X ⟶ X) (hu : u ≫ xBase = xBase) :
    projectiveUniversalFiniteIncidenceParameterReindex R xBase tBase u hu ≫
      pullback.fst xBase tBase = pullback.fst xBase tBase ≫ u :=
  by
    unfold projectiveUniversalFiniteIncidenceParameterReindex
    exact pullback.lift_fst _ _ _

/-- Reindexing leaves the equation parameter unchanged. -/
theorem projectiveUniversalFiniteIncidenceParameterReindex_snd
    {X T : Scheme.{u}}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (u : X ⟶ X) (hu : u ≫ xBase = xBase) :
    projectiveUniversalFiniteIncidenceParameterReindex R xBase tBase u hu ≫
      pullback.snd xBase tBase = pullback.snd xBase tBase :=
  by
    unfold projectiveUniversalFiniteIncidenceParameterReindex
    exact pullback.lift_snd _ _ _

/-- The same reindexing identity written using the named projection of the
finite-incidence parameter space. -/
theorem projectiveUniversalFiniteIncidenceParameterReindex_projection
    {X T : Scheme.{u}}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (u : X ⟶ X) (hu : u ≫ xBase = xBase) :
    projectiveUniversalFiniteIncidenceParameterReindex R xBase tBase u hu ≫
      projectiveUniversalFiniteIncidenceParameterProjection R xBase tBase =
        projectiveUniversalFiniteIncidenceParameterProjection R xBase tBase ≫ u := by
  exact projectiveUniversalFiniteIncidenceParameterReindex_fst R xBase tBase u hu

/-- If an endomorphism permutes the marked ambient maps, then its induced
map of parameter spaces permutes the corresponding universal incidences. -/
theorem projectiveUniversalFiniteIncidenceParameterReindex_map
    {X T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d)
    (u : X ⟶ X) (hu : u ≫ xBase = xBase)
    (e : Equiv.Perm ι)
    (ha : ∀ i, u ≫ a i = a (e i)) (i : ι) :
    projectiveUniversalFiniteIncidenceParameterReindex R xBase tBase u hu ≫
      projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i =
        projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s (e i) := by
  apply Limits.prod.hom_ext
  · simp only [Category.assoc, projectiveUniversalFiniteIncidenceParameterMap,
      Limits.prod.lift_fst]
    rw [← Category.assoc,
      projectiveUniversalFiniteIncidenceParameterReindex_fst,
      Category.assoc, ha]
  · simp only [Category.assoc, projectiveUniversalFiniteIncidenceParameterMap,
      Limits.prod.lift_snd]
    rw [← Category.assoc,
      projectiveUniversalFiniteIncidenceParameterReindex_snd]

/-- A base endomorphism that permutes the marked points preserves the finite
universal-incidence bad locus. -/
theorem mapsTo_projectiveUniversalFiniteIncidenceBadLocus
    {X T : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ Spec (.of R)) (tBase : T ⟶ Spec (.of R))
    (a : ι → (X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)))
    (s : T ⟶ projectiveParameters R σ d)
    (u : X ⟶ X) (hu : u ≫ xBase = xBase)
    (e : Equiv.Perm ι)
    (ha : ∀ i, u ≫ a i = a (e i)) :
    Set.MapsTo u
      (projectiveUniversalFiniteIncidenceBadLocus R σ d xBase tBase a s)
      (projectiveUniversalFiniteIncidenceBadLocus R σ d xBase tBase a s) := by
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hx
  refine ⟨projectiveUniversalFiniteIncidenceParameterReindex R xBase tBase u hu z, ?_, ?_⟩
  · apply Set.mem_iInter.mpr
    intro i
    have hi := (Set.mem_iInter.mp hz) (e i)
    change (projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i)
      (projectiveUniversalFiniteIncidenceParameterReindex R xBase tBase u hu z) ∈
        Set.range (projectiveUniversalIncidence R σ d)
    have hmap := congrArg (fun k => k z)
      (projectiveUniversalFiniteIncidenceParameterReindex_map R σ d
        xBase tBase a s u hu e ha i)
    change (projectiveUniversalFiniteIncidenceParameterReindex R xBase tBase u hu ≫
      projectiveUniversalFiniteIncidenceParameterMap R σ d xBase tBase a s i) z ∈
        Set.range (projectiveUniversalIncidence R σ d)
    rw [hmap]
    exact hi
  · change (projectiveUniversalFiniteIncidenceParameterReindex R xBase tBase u hu ≫
      projectiveUniversalFiniteIncidenceParameterProjection R xBase tBase) z = u x
    rw [projectiveUniversalFiniteIncidenceParameterReindex_projection]
    exact congrArg u hzx

end UniversalHomogeneous
end AllCharacteristics
