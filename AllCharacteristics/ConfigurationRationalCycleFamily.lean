import AllCharacteristics.ProjectiveConfigurationFiberCycle
import AllCharacteristics.ProjectiveConfigurationFiberSubscheme
import PfaffianDescent.RationalCycleFamilies
import PfaffianDescent.FiniteSchemeFundamentalIso

/-!
# Curve maps into configuration spaces give rational cycle families

The unordered distinct configuration quotient carries the universal finite
étale incidence scheme.  Pulling that incidence scheme back along a map from
the projective line produces exactly the finite-flat curve family used by the
cycle quotient.  This is the scheme-theoretic bridge needed when a geometric
construction is first described as a curve in a configuration parameter
space.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits PfaffianDescent
namespace AllCharacteristics
namespace HomogeneousProjective

universe u v

variable {A : Type u} [CommRing A]
variable {K : Type u} [Field K]
variable {sigma : Type v} [SetLike sigma A] [AddSubgroupClass sigma A]
variable (graded : ℕ → sigma) [GradedRing graded]
variable (f : Proj graded ⟶ Spec (.of K)) [IsSeparated f]

/- An ordered tuple curve already carries a finite-flat cycle family, even
   when coordinates collide.  The disjoint union in the source records the
   summands with their scheme-theoretic multiplicities, so this construction
   extends the distinct-configuration version below to the full ordered
   relative power.  Its fibers at `K`-rational endpoints are split; the
   general degree-ten argument therefore uses `RationalCycleFamily` directly
   when it must also accommodate a non-split closed point. -/
noncomputable def rationalCycleFamily_of_orderedTupleCurve
    (n : ℕ)
    (t : projectiveLineProj K ⟶ (orderedFamilyPowerOver f n).left)
    (ht : t ≫ (orderedFamilyPowerOver f n).hom = projectiveLineProjToBase K) :
    PfaffianDescent.RationalCycleFamily f := by
  let ι := ULift.{u} (Fin n)
  let curve : Scheme.{u} := ∐ fun _ : ι => projectiveLineProj K
  let toLine : curve ⟶ projectiveLineProj K := constantCoverToBase ι
    (projectiveLineProj K)
  let toScheme : curve ⟶ Proj graded := Sigma.desc (fun i : ι =>
    t ≫ (orderedFamilyCoordinate f n i.down).left)
  have hfinite : IsFinite toLine := by
    dsimp [toLine]
    exact isFinite_constantCoverToBase ι (projectiveLineProj K)
  have hflat : Flat toLine := by
    dsimp [toLine]
    exact flat_constantCoverToBase ι (projectiveLineProj K)
  have hlfp : LocallyOfFinitePresentation toLine := by
    letI : Etale toLine := by
      dsimp [toLine]
      exact etale_constantCoverToBase ι (projectiveLineProj K)
    infer_instance
  have hover : toScheme ≫ f = toLine ≫ projectiveLineProjToBase K := by
    apply Sigma.hom_ext
    intro i
    dsimp [toScheme, toLine, constantCoverToBase]
    rw [← Category.assoc, Sigma.ι_desc, ← Category.assoc, Sigma.ι_desc,
      Category.assoc, orderedFamilyCoordinate_toBase, ht]
    simp
  exact
    { curve := curve
      toLine := toLine
      finite := hfinite
      flat := hflat
      finitelyPresented := hlfp
      toScheme := toScheme
      overBase := hover }

theorem rationalCycleFamily_of_orderedTupleCurve_fiberCycle_degree
    (n : ℕ)
    (t : projectiveLineProj K ⟶ (orderedFamilyPowerOver f n).left)
    (ht : t ≫ (orderedFamilyPowerOver f n).hom = projectiveLineProjToBase K)
    (b : Bool) :
    EffectiveZeroCycle.degree f
        ((rationalCycleFamily_of_orderedTupleCurve graded f n t ht).fiberCycle b) = n := by
  rw [PfaffianDescent.RationalCycleFamily.fiberCycle_degree]
  change (constantCoverToBase (ULift.{u} (Fin n)) (projectiveLineProj K)).finrank
      (projectiveLineEndpoint K b (IsLocalRing.closedPoint K)) = n
  rw [finrank_constantCoverToBase]
  simp

/-- A projective-line map into the unordered configuration quotient pulls the
universal incidence scheme back to a `RationalCycleFamily`.  The map `hc`
records that the configuration curve lies over the fixed coefficient field.
-/
noncomputable def rationalCycleFamily_of_configurationCurve
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K) :
    PfaffianDescent.RationalCycleFamily f := by
  let q := projectiveConfigurationIncidenceToBase graded f n
  let a := projectiveConfigurationIncidenceToProjective graded f n
  let curve := pullback q c
  let toLine : curve ⟶ projectiveLineProj K := pullback.snd q c
  let toScheme : curve ⟶ Proj graded := pullback.fst q c ≫ a
  have hfinite : IsFinite toLine := by
    dsimp [toLine, q]
    infer_instance
  have hflat : Flat toLine := by
    dsimp [toLine, q]
    infer_instance
  have hlfp : LocallyOfFinitePresentation toLine := by
    dsimp [toLine, q]
    infer_instance
  have hover : toScheme ≫ f = toLine ≫ projectiveLineProjToBase K := by
    dsimp [toScheme, toLine, a, q]
    rw [Category.assoc, projectiveConfigurationIncidenceToProjective_toBase]
    rw [← Category.assoc, pullback.condition, Category.assoc, hc]
  exact
    { curve := curve
      toLine := toLine
      finite := hfinite
      flat := hflat
      finitelyPresented := hlfp
      toScheme := toScheme
      overBase := hover }

/-- The pulled-back incidence family has the prescribed configuration rank at
each endpoint of the projective line. -/
theorem rationalCycleFamily_of_configurationCurve_toLine_finrank
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (b : Bool) :
    (rationalCycleFamily_of_configurationCurve graded f n c hc).toLine.finrank
        (projectiveLineEndpoint K b (IsLocalRing.closedPoint K)) = n := by
  let q := projectiveConfigurationIncidenceToBase graded f n
  have h := Scheme.Hom.finrank_of_isPullback
    (pullback.fst q c) (pullback.snd q c) q c (IsPullback.of_hasPullback q c)
      (projectiveLineEndpoint K b (IsLocalRing.closedPoint K))
  change (pullback.snd q c).finrank
      (projectiveLineEndpoint K b (IsLocalRing.closedPoint K)) = n
  rw [h]
  exact finrank_projectiveConfigurationIncidenceToBase graded f n
    (c (projectiveLineEndpoint K b (IsLocalRing.closedPoint K)))

/-- Consequently, both endpoint cycles of the configuration family have
scheme-theoretic degree `n`. -/
theorem rationalCycleFamily_of_configurationCurve_fiberCycle_degree
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (b : Bool) :
    EffectiveZeroCycle.degree f
        ((rationalCycleFamily_of_configurationCurve graded f n c hc).fiberCycle b) = n := by
  rw [RationalCycleFamily.fiberCycle_degree]
  exact rationalCycleFamily_of_configurationCurve_toLine_finrank graded f n c hc b

/-- Each endpoint of a curve in the distinct unordered configuration space
also carries its actual finite-subscheme datum on the original projective
fiber.  This retains the ideal-defined subscheme alongside the endpoint
cycle used by the rational-equivalence calculation. -/
noncomputable def projectiveConfigurationCurveEndpointFiniteSubscheme
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (b : Bool) :
    FiniteSubschemeDatum f n :=
  projectiveConfigurationFiniteSubschemeAt graded f n
    (projectiveLineEndpoint K b ≫ c) (by
      rw [Category.assoc, hc, projectiveLineEndpoint_toBase])

/- The endpoint of the pulled-back incidence family is canonically the direct
incidence fiber over the endpoint configuration.  The construction uses
pullback associativity followed by the isomorphism obtained from the identity
pullback on the projective line. -/
noncomputable def configurationCurveFiberIso
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (b : Bool) :
    pullback (pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c)
      (projectiveLineEndpoint K b) ≅
      projectiveConfigurationFiber graded f n
        (projectiveLineEndpoint K b ≫ c) := by
  let q := projectiveConfigurationIncidenceToBase graded f n
  let e := projectiveLineEndpoint K b
  let assocIso := pullbackAssoc q c (𝟙 _) e
  let g3 := pullback.fst (𝟙 (projectiveLineProj K)) e
  let g4 := pullback.snd (𝟙 (projectiveLineProj K)) e
  let eq1 : q ≫ 𝟙 _ = 𝟙 _ ≫ q := by simp
  let eq2 : (g3 ≫ c) ≫ 𝟙 _ = g4 ≫ (e ≫ c) := by
    dsimp [g3, g4]
    rw [Category.comp_id, ← Category.assoc, ← pullback.condition]
    rfl
  let m := pullback.map q (g3 ≫ c) q (e ≫ c) (𝟙 _) g4 (𝟙 _) eq1 eq2
  haveI : IsIso g4 := by
    dsimp [g4]
    infer_instance
  haveI : IsIso m := by
    dsimp [m]
    infer_instance
  exact assocIso ≪≫ asIso m

lemma configurationCurveFiberIso_hom_fst
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (b : Bool) :
    (configurationCurveFiberIso graded f n c b).hom ≫
      pullback.fst (projectiveConfigurationIncidenceToBase graded f n)
        (projectiveLineEndpoint K b ≫ c) =
    pullback.fst (pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c)
      (projectiveLineEndpoint K b) ≫
      pullback.fst (projectiveConfigurationIncidenceToBase graded f n) c := by
  let q := projectiveConfigurationIncidenceToBase graded f n
  let e := projectiveLineEndpoint K b
  let assocIso := pullbackAssoc q c (𝟙 _) e
  let g3 := pullback.fst (𝟙 (projectiveLineProj K)) e
  let g4 := pullback.snd (𝟙 (projectiveLineProj K)) e
  let eq1 : q ≫ 𝟙 _ = 𝟙 _ ≫ q := by simp
  let eq2 : (g3 ≫ c) ≫ 𝟙 _ = g4 ≫ (e ≫ c) := by
    dsimp [g3, g4]
    rw [Category.comp_id, ← Category.assoc, ← pullback.condition]
    rfl
  let m := pullback.map q (g3 ≫ c) q (e ≫ c) (𝟙 _) g4 (𝟙 _) eq1 eq2
  have hm : m ≫ pullback.fst q (e ≫ c) = pullback.fst q (g3 ≫ c) ≫ 𝟙 _ := by
    change pullback.lift _ _ _ ≫ pullback.fst q (e ≫ c) = _
    rw [pullback.lift_fst]
  have hmf : m ≫ pullback.fst q (e ≫ c) = pullback.fst q (g3 ≫ c) := by
    simpa using hm
  have ha := pullbackAssoc_hom_fst q c (𝟙 _) e
  change (assocIso.hom ≫ (asIso m).hom) ≫ pullback.fst q (e ≫ c) = _
  dsimp [asIso]
  rw [Category.assoc, hmf]
  change assocIso.hom ≫ pullback.fst q (g3 ≫ c) =
    pullback.fst (pullback.snd q c ≫ 𝟙 _) e ≫ pullback.fst q c
  change (pullbackAssoc q c (𝟙 _) e).hom ≫
      pullback.fst q (pullback.fst (𝟙 _) e ≫ c) = _
  exact pullbackAssoc_hom_fst q c (𝟙 _) e

lemma configurationCurveFiberIso_hom_snd
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (b : Bool) :
    (configurationCurveFiberIso graded f n c b).hom ≫
      pullback.snd (projectiveConfigurationIncidenceToBase graded f n)
        (projectiveLineEndpoint K b ≫ c) =
    pullback.snd (pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c)
      (projectiveLineEndpoint K b) := by
  let q := projectiveConfigurationIncidenceToBase graded f n
  let e := projectiveLineEndpoint K b
  let assocIso := pullbackAssoc q c (𝟙 _) e
  let g3 := pullback.fst (𝟙 (projectiveLineProj K)) e
  let g4 := pullback.snd (𝟙 (projectiveLineProj K)) e
  let eq1 : q ≫ 𝟙 _ = 𝟙 _ ≫ q := by simp
  let eq2 : (g3 ≫ c) ≫ 𝟙 _ = g4 ≫ (e ≫ c) := by
    dsimp [g3, g4]
    rw [Category.comp_id, ← Category.assoc, ← pullback.condition]
    rfl
  let m := pullback.map q (g3 ≫ c) q (e ≫ c) (𝟙 _) g4 (𝟙 _) eq1 eq2
  have hm : m ≫ pullback.snd q (e ≫ c) = pullback.snd q (g3 ≫ c) ≫ g4 := by
    change pullback.lift _ _ _ ≫ pullback.snd q (e ≫ c) = _
    rw [pullback.lift_snd]
  have ha := pullbackAssoc_hom_snd_snd q c (𝟙 _) e
  change (assocIso.hom ≫ (asIso m).hom) ≫ pullback.snd q (e ≫ c) = _
  dsimp [asIso]
  rw [Category.assoc, hm]
  change assocIso.hom ≫ pullback.snd q (g3 ≫ c) ≫ g4 = _
  change (pullbackAssoc q c (𝟙 _) e).hom ≫
      pullback.snd q (pullback.fst (𝟙 _) e ≫ c) ≫
      pullback.snd (𝟙 _) e = _
  exact pullbackAssoc_hom_snd_snd q c (𝟙 _) e

lemma configurationCurveFiberIso_hom_toProjective
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (b : Bool) :
    (configurationCurveFiberIso graded f n c b).hom ≫
      projectiveConfigurationFiberToProjective graded f n
        (projectiveLineEndpoint K b ≫ c) =
      (rationalCycleFamily_of_configurationCurve graded f n c hc).fiberToScheme b := by
  change (configurationCurveFiberIso graded f n c b).hom ≫
      pullback.fst (projectiveConfigurationIncidenceToBase graded f n)
        (projectiveLineEndpoint K b ≫ c) ≫
      projectiveConfigurationIncidenceToProjective graded f n =
    pullback.fst (pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c)
      (projectiveLineEndpoint K b) ≫
      (pullback.fst (projectiveConfigurationIncidenceToBase graded f n) c ≫
        projectiveConfigurationIncidenceToProjective graded f n)
  rw [← Category.assoc, configurationCurveFiberIso_hom_fst graded f n c b]
  simp [Category.assoc]

lemma rationalCycleFamily_of_configurationCurve_fiberCycle_eq_projectiveConfigurationCycle
    (n : ℕ)
    (c : projectiveLineProj K ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n =
      projectiveLineProjToBase K)
    (b : Bool) :
    (rationalCycleFamily_of_configurationCurve graded f n c hc).fiberCycle b =
      projectiveConfigurationCycle graded f n
        (projectiveLineEndpoint K b ≫ c) (by
          rw [Category.assoc, hc, projectiveLineEndpoint_toBase]) := by
  let F : RationalCycleFamily f :=
    rationalCycleFamily_of_configurationCurve graded f n c hc
  let q := projectiveConfigurationIncidenceToBase graded f n
  let e := configurationCurveFiberIso graded f n c b
  let g := projectiveConfigurationFiberToProjective graded f n
    (projectiveLineEndpoint K b ≫ c)
  let gbase := pullback.snd q (projectiveLineEndpoint K b ≫ c)
  have hbase : (projectiveLineEndpoint K b ≫ c) ≫
      projectiveConfigurationQuotientToBase graded f n = 𝟙 _ := by
    rw [Category.assoc, hc, projectiveLineEndpoint_toBase]
  letI : IsFinite g := projectiveConfigurationFiberToProjective_isFinite graded f n
    (projectiveLineEndpoint K b ≫ c) hbase
  have hmap : e.hom ≫ g = F.fiberToScheme b := by
    simpa [e, g, F] using
      configurationCurveFiberIso_hom_toProjective graded f n c hc b
  have hbaseiso : e.hom ≫ gbase = pullback.snd F.toLine
      (projectiveLineEndpoint K b) := by
    change e.hom ≫ gbase = pullback.snd (pullback.snd q c)
      (projectiveLineEndpoint K b)
    simpa [e, gbase] using configurationCurveFiberIso_hom_snd graded f n c b
  have h := PfaffianDescent.fiberCycle_eq_pushforward_of_iso f F b e g gbase hmap hbaseiso
  simpa [F, g, gbase, projectiveConfigurationCycle] using h

end HomogeneousProjective
end AllCharacteristics
