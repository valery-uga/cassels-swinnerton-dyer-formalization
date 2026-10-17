import AllCharacteristics.ProjectiveGaloisOrbitConfiguration
import AllCharacteristics.ProjectiveConfigurationFiberCycle
import AllCharacteristics.ProjectiveConfigurationCurveFiniteSubscheme
import AllCharacteristics.ClosedPointFiniteSubschemeCycle
import PfaffianDescent.ResidualCycles

/-!
# A closed point as its unordered configuration cycle

Over a characteristic-zero field, a closed point is finite separable.  Its
Galois orbit gives a rational point of the unordered distinct-configuration
space.  This file proves that the scheme-theoretic incidence cycle at that
configuration point is the original closed point with multiplicity one.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u v

variable {A : Type u} [CommRing A] {sigma : Type v} [SetLike sigma A]
  [AddSubgroupClass sigma A]
variable (graded : ℕ → sigma) [GradedRing graded]
variable {K : Type u} [Field K] [CharZero K]

/-- A closed point in a characteristic-zero projective family is represented
by an actual rational unordered configuration, and the fundamental cycle of
the universal incidence fiber is exactly that closed point. -/
theorem exists_projectiveConfigurationCycle_eq_closedPoint
    (f : Proj graded ⟶ Spec (.of K)) [IsSeparated f] [LocallyOfFiniteType f]
    (x : closedPoints (Proj graded)) (n : ℕ)
    (hx : f.residueDegree x.1 = n) :
    ∃ (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen graded f n).toScheme)
      (hc : c ≫ projectiveConfigurationQuotientToBase graded f n = 𝟙 _),
      projectiveConfigurationCycle graded f n c hc = Finsupp.single x 1 := by
  let E : Type u := (Proj graded).residueField x.1
  letI : Field E := inferInstanceAs (Field ((Proj graded).residueField x.1))
  letI : Algebra K E := pointAlgebra f x.1
  haveI : FiniteDimensional K E := closedPoint_moduleFinite f x
  haveI : Algebra.IsSeparable K E := inferInstance
  let q : Spec (.of E) ⟶ Proj graded := (Proj graded).fromSpecResidueField x.1
  haveI : IsClosedImmersion q := by
    dsimp only [q]
    exact isClosed_singleton_iff_isClosedImmersion.mp x.2
  have hn : Module.finrank K E = n :=
    (closedPoint_finrank_eq_residueDegree f x).trans hx
  let Omega : Type u := AlgebraicClosure K
  letI : Field Omega := inferInstanceAs (Field (AlgebraicClosure K))
  letI : Algebra K Omega := inferInstanceAs (Algebra K (AlgebraicClosure K))
  let emb : E →ₐ[K] Omega := IsAlgClosed.lift
  letI : Algebra E Omega := emb.toRingHom.toAlgebra
  letI : IsScalarTower K E Omega := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    exact (emb.commutes r).symm
  let L : Type u := IntermediateField.normalClosure K E Omega
  letI : Field L := inferInstanceAs (Field (IntermediateField.normalClosure K E Omega))
  letI : Algebra K L := inferInstanceAs
    (Algebra K (IntermediateField.normalClosure K E Omega))
  letI : Algebra E L := inferInstanceAs
    (Algebra E (IntermediateField.normalClosure K E Omega))
  letI : IsScalarTower K E L := inferInstanceAs
    (IsScalarTower K E (IntermediateField.normalClosure K E Omega))
  letI : FiniteDimensional K L := inferInstanceAs
    (FiniteDimensional K (IntermediateField.normalClosure K E Omega))
  letI : IsGalois K L := inferInstanceAs
    (IsGalois K (IntermediateField.normalClosure K E Omega))
  have hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ 𝟙 _ := by
    simpa only [Category.comp_id] using (pointAlgebra_spec f x.1).symm
  obtain ⟨c, a, hc, hca, hcoord⟩ :=
    exists_projectiveConfigurationPoint_of_galoisOrbit_with_orderedLift
      graded f (K := K) (E := E) (L := L) n hn (𝟙 _) q hq
  refine ⟨c, hc, ?_⟩
  let toK := pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c
  let toX := projectiveConfigurationFiberToProjective graded f n c
  let z := projectiveConfigurationCycle graded f n c hc
  haveI : IsFinite toX :=
    projectiveConfigurationFiberToProjective_isFinite graded f n c hc
  have hsuppSet : ↑z.support ⊆ ({x} : Set (closedPoints (Proj graded))) := by
    intro y hy
    have hyrange : y ∈ Set.range (universallyClosedPointMap toX) := by
      apply pushforwardCycle_support_subset_range toX
        (PfaffianDescent.finiteSchemeFundamentalCycle toK)
      exact hy
    obtain ⟨s, hs⟩ := hyrange
    apply Subtype.ext
    let iy := pullback.fst (projectiveConfigurationIncidenceToBase graded f n) c s.1
    have hpull := congrArg (fun h ↦ h s.1)
      (pullback.condition :
        pullback.fst (projectiveConfigurationIncidenceToBase graded f n) c ≫
            projectiveConfigurationIncidenceToBase graded f n =
          pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c ≫ c)
    change projectiveConfigurationIncidenceToBase graded f n iy =
      c (pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c s.1) at hpull
    have hsnd : pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c s.1 =
        IsLocalRing.closedPoint K := Subsingleton.elim _ _
    have hcaPoint := congrArg (fun h ↦ h (IsLocalRing.closedPoint L)) hca
    change c (Spec.map (CommRingCat.ofHom (algebraMap K L))
        (IsLocalRing.closedPoint L)) =
      projectiveConfigurationQuotientMap graded f n
        (a (IsLocalRing.closedPoint L)) at hcaPoint
    have hpi : Spec.map (CommRingCat.ofHom (algebraMap K L))
        (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [hpi] at hcaPoint
    have hiybase : projectiveConfigurationIncidenceToBase graded f n iy =
        projectiveConfigurationQuotientMap graded f n
          (a (IsLocalRing.closedPoint L)) := by
      calc
        _ = c (pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c s.1) := hpull
        _ = c (IsLocalRing.closedPoint K) := congrArg c hsnd
        _ = _ := hcaPoint
    obtain ⟨i, hi⟩ := projectiveConfigurationIncidence_point_eq_coordinate
      graded f n (a (IsLocalRing.closedPoint L)) iy hiybase
    have hcoordPoint := congrArg (fun h ↦ h (IsLocalRing.closedPoint L)) (hcoord i)
    change ((orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n i).left) (a (IsLocalRing.closedPoint L)) =
      q (Spec.map (CommRingCat.ofHom
        ((galoisEmbeddingIndex K E L n hn) i).toRingHom)
          (IsLocalRing.closedPoint L)) at hcoordPoint
    have hepoint : Spec.map (CommRingCat.ofHom
        ((galoisEmbeddingIndex K E L n hn) i).toRingHom)
          (IsLocalRing.closedPoint L) = IsLocalRing.closedPoint E := Subsingleton.elim _ _
    rw [hepoint] at hcoordPoint
    have hqx : q (IsLocalRing.closedPoint E) = x.1 := by
      exact (Proj graded).fromSpecResidueField_apply x.1 (IsLocalRing.closedPoint E)
    have hsval := congrArg Subtype.val hs
    exact (hsval.symm.trans <| by
      change toX s.1 = x.1
      calc
        toX s.1 = projectiveConfigurationIncidenceToProjective graded f n iy := rfl
        _ = ((orderedFamilyConfigurationOpen f n).ι ≫
            (orderedFamilyCoordinate f n i).left) (a (IsLocalRing.closedPoint L)) := hi
        _ = q (IsLocalRing.closedPoint E) := hcoordPoint
        _ = x.1 := hqx)
  have hsupp : z.support ⊆ {x} := by
    exact Finset.coe_subset.mp (by simpa only [Finset.coe_singleton] using hsuppSet)
  have hzsingle : z = Finsupp.single x (z x) :=
    Finsupp.support_subset_singleton.mp hsupp
  have hzdegree := projectiveConfigurationCycle_degree graded f n c hc
  change EffectiveZeroCycle.degree f z = n at hzdegree
  rw [hzsingle, PfaffianDescent.effectiveCycle_degree_single, hx] at hzdegree
  have hnpos : 0 < n := by
    rw [← hn]
    exact Module.finrank_pos
  have hcoeff : z x = 1 := by
    apply mul_right_cancel₀ hnpos.ne'
    simpa using hzdegree
  change z = Finsupp.single x 1
  rw [hzsingle, hcoeff]

/-- The configuration cycle of a non-split closed point agrees with the
canonical ideal-defined finite-subscheme cycle of that point.  Thus Coray's
degree-ten alternative can enter the configuration-space part of Voisin's
argument without replacing the closed point by a split tuple of rational
points. -/
theorem exists_projectiveConfigurationCycle_eq_closedPointDatumCycle
    (f : Proj graded ⟶ Spec (.of K)) [IsSeparated f] [LocallyOfFiniteType f]
    (x : closedPoints (Proj graded)) (n : ℕ)
    (hx : f.residueDegree x.1 = n) :
    ∃ (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen graded f n).toScheme)
      (hc : c ≫ projectiveConfigurationQuotientToBase graded f n = 𝟙 _),
      projectiveConfigurationCycle graded f n c hc =
        finiteSubschemeDatumCycle f
          (finiteSubschemeDatumOfClosedPointOfResidueDegree f x n hx) := by
  obtain ⟨c, hc, hcycle⟩ :=
    exists_projectiveConfigurationCycle_eq_closedPoint graded f x n hx
  refine ⟨c, hc, ?_⟩
  rw [hcycle, finiteSubschemeDatumCycle_closedPoint_of_residueDegree f x n hx]

/-- A closed point of residue degree `n` is the endpoint cycle of an actual
finite-flat pencil obtained from its unordered configuration.  The pencil is
constant here; its role is to retain the ideal-defined finite subschemes that
the later nonconstant Voisin constructions must move.  In particular this
works for Coray's non-split degree-ten alternative. -/
theorem exists_constantConfigurationPencil_endpointCycle_eq_closedPoint
    (f : Proj graded ⟶ Spec (.of K)) [IsSeparated f] [LocallyOfFiniteType f]
    (x : closedPoints (Proj graded)) (n : ℕ)
    (hx : f.residueDegree x.1 = n) :
    ∃ (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen graded f n).toScheme)
      (hc : c ≫ projectiveConfigurationQuotientToBase graded f n = 𝟙 _),
      ∀ b : Bool,
        finiteSubschemeDatumCycle f
          (finiteSubschemeDatumAtLineEndpoint f n
            (HomogeneousProjective.projectiveConfigurationCurveFiniteSubscheme graded f n
              (HomogeneousProjective.projectiveConfigurationConstantCurve graded f n c)
              (HomogeneousProjective.projectiveConfigurationConstantCurve_toBase
                graded f n c hc)) b) = Finsupp.single x 1 := by
  obtain ⟨c, hc, hcycle⟩ :=
    exists_projectiveConfigurationCycle_eq_closedPoint graded f x n hx
  refine ⟨c, hc, ?_⟩
  intro b
  rw [HomogeneousProjective.finiteSubschemeDatumAtLineEndpoint_constantConfigurationCurve_cycle
    graded f n c hc b, hcycle]

end AllCharacteristics
