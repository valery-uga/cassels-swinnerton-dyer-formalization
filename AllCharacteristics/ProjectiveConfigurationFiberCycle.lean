import AllCharacteristics.ProjectiveConfigurationIncidenceFiniteEtale
import AllCharacteristics.ProperCyclePushforward
import PfaffianDescent.IntrinsicFiniteCycle

/-!
# The cycle represented by an unordered projective configuration

The universal incidence subscheme over the unordered configuration quotient
is finite flat of rank `n`.  Pulling it back to a field-valued configuration
and pushing its intrinsic fundamental cycle into the original projective
family gives the effective zero-cycle represented by that configuration.

Keeping this construction scheme-theoretic is important for Voisin's
specialization argument: multiplicities are the lengths of the actual local
rings, rather than a set-theoretic count of geometric points.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u v

variable {A : Type u} [CommRing A] {sigma : Type v} [SetLike sigma A]
  [AddSubgroupClass sigma A]
variable (graded : ℕ → sigma) [GradedRing graded]
variable {K : Type u} [Field K]
variable (f : Proj graded ⟶ Spec (.of K)) [IsSeparated f]

/-- The incidence subscheme remembers its point in the original projective
family. -/
noncomputable def projectiveConfigurationIncidenceToProjective (n : ℕ) :
    projectiveConfigurationIncidence graded f n ⟶ Proj graded :=
  projectiveConfigurationIncidenceι graded f n ≫
    pullback.fst f (projectiveConfigurationQuotientToBase graded f n)

lemma projectiveConfigurationIncidenceToProjective_toBase (n : ℕ) :
    projectiveConfigurationIncidenceToProjective graded f n ≫ f =
      projectiveConfigurationIncidenceToBase graded f n ≫
        projectiveConfigurationQuotientToBase graded f n := by
  unfold projectiveConfigurationIncidenceToProjective
  unfold projectiveConfigurationIncidenceToBase
  let i := projectiveConfigurationIncidenceι graded f n
  let q := projectiveConfigurationQuotientToBase graded f n
  have hp :
      (show projectiveConfigurationFamily graded f n ⟶ Proj graded from
          pullback.fst f q) ≫ f =
        (show projectiveConfigurationFamily graded f n ⟶
            (projectiveConfigurationQuotientOpen graded f n).toScheme from
          pullback.snd f q) ≫ q := by
    simpa only [projectiveConfigurationFamily] using
      (pullback.condition : pullback.fst f q ≫ f = pullback.snd f q ≫ q)
  calc
    (i ≫ pullback.fst f q) ≫ f = i ≫ (pullback.fst f q ≫ f) :=
      Category.assoc _ _ _
    _ = i ≫ (pullback.snd f q ≫ q) := congrArg (i ≫ ·) hp
    _ = (i ≫ pullback.snd f q) ≫ q := Category.assoc _ _ _ |>.symm

/-- On the component marked by `i`, the incidence point is exactly the
`i`-th coordinate of the ordered configuration. -/
@[reassoc]
lemma projectiveConfigurationMarkedToIncidence_toProjective (n : ℕ) (i : Fin n) :
    Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ (orderedFamilyConfigurationOver f n).left)
        (ULift.up i) ≫
        projectiveConfigurationMarkedToIncidence graded f n ≫
          projectiveConfigurationIncidenceToProjective graded f n =
      (orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n i).left := by
  let mark : (orderedFamilyConfigurationOver f n).left ⟶
      orderedConfigurationMarkedSource f n :=
    Sigma.ι (fun _ : ULift.{u} (Fin n) ↦
      (orderedFamilyConfigurationOver f n).left) (ULift.up i)
  let r := projectiveConfigurationMarkedToIncidence graded f n
  let inc := projectiveConfigurationIncidenceι graded f n
  let u := orderedConfigurationUnionMap f n
  let F := projectiveConfigurationFamilyMap graded f n
  let fstQ : projectiveConfigurationFamily graded f n ⟶ Proj graded :=
    pullback.fst f (projectiveConfigurationQuotientToBase graded f n)
  let fstC := pullback.fst f (orderedFamilyConfigurationOver f n).hom
  have hr : r ≫ inc = projectiveConfigurationMarkedMap graded f n :=
    projectiveConfigurationMarkedToIncidence_ι graded f n
  have hF : F ≫ fstQ = fstC := baseChangedFamilyMap_fst _ _ _ _ _
  have hu : mark ≫ u = orderedConfigurationSection f n i :=
    Sigma.ι_desc _ (ULift.up i)
  have hs : orderedConfigurationSection f n i ≫ fstC =
      (orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n i).left :=
    orderedConfigurationSection_fst f n i
  have hri : (mark ≫ r) ≫ inc =
      mark ≫ projectiveConfigurationMarkedMap graded f n := by
    calc
      (mark ≫ r) ≫ inc = mark ≫ (r ≫ inc) := Category.assoc _ _ _
      _ = mark ≫ projectiveConfigurationMarkedMap graded f n :=
        congrArg (mark ≫ ·) hr
  have hpre : (mark ≫ r) ≫
      projectiveConfigurationIncidenceToProjective graded f n =
      orderedConfigurationSection f n i ≫ fstC := by
    calc
      (mark ≫ r) ≫ projectiveConfigurationIncidenceToProjective graded f n =
        ((mark ≫ r) ≫ inc) ≫ fstQ := rfl
      _ = (mark ≫ projectiveConfigurationMarkedMap graded f n) ≫ fstQ :=
        congrArg (· ≫ fstQ) hri
      _ = ((mark ≫ u) ≫ F) ≫ fstQ := rfl
      _ = (mark ≫ u) ≫ (F ≫ fstQ) := Category.assoc _ _ _
      _ = (mark ≫ u) ≫ fstC := congrArg ((mark ≫ u) ≫ ·) hF
      _ = orderedConfigurationSection f n i ≫ fstC := congrArg (· ≫ fstC) hu
  exact hpre.trans hs

/-- A point of the unordered incidence over the orbit of an ordered
configuration is one of that configuration's coordinates.  This is the
pointwise support statement behind the Galois-orbit cycle calculation. -/
theorem projectiveConfigurationIncidence_point_eq_coordinate (n : ℕ)
    (a : (orderedFamilyConfigurationOver f n).left)
    (y : projectiveConfigurationIncidence graded f n)
    (hy : projectiveConfigurationIncidenceToBase graded f n y =
      projectiveConfigurationQuotientMap graded f n a) :
    ∃ i : Fin n,
      projectiveConfigurationIncidenceToProjective graded f n y =
        ((orderedFamilyConfigurationOpen f n).ι ≫
          (orderedFamilyCoordinate f n i).left) a := by
  let r := projectiveConfigurationMarkedToIncidence graded f n
  let q := projectiveConfigurationQuotientMap graded f n
  obtain ⟨m, hm⟩ := r.surjective y
  let e := sigmaMk (fun _ : ULift.{u} (Fin n) ↦
    (orderedFamilyConfigurationOver f n).left)
  generalize heq : e.symm m = it
  obtain ⟨⟨j⟩, t⟩ := it
  have hmt : Sigma.ι
      (fun _ : ULift.{u} (Fin n) ↦ (orderedFamilyConfigurationOver f n).left)
        (ULift.up j) t = m := by
    rw [← sigmaMk_mk]
    exact (congrArg e heq.symm).trans (e.apply_symm_apply m)
  have hbaseMor := projectiveConfigurationMarkedToIncidence_toBase graded f n
  let mark : (orderedFamilyConfigurationOver f n).left ⟶
      orderedConfigurationMarkedSource f n :=
    Sigma.ι (fun _ : ULift.{u} (Fin n) ↦
      (orderedFamilyConfigurationOver f n).left) (ULift.up j)
  have hmarkBase : mark ≫ constantCoverToBase (ULift.{u} (Fin n))
      (orderedFamilyConfigurationOver f n).left =
      𝟙 (orderedFamilyConfigurationOver f n).left := by
    exact Sigma.ι_desc _ (ULift.up j)
  have hbaseMor' : (mark ≫ r) ≫ projectiveConfigurationIncidenceToBase graded f n = q := by
    calc
      (mark ≫ r) ≫ projectiveConfigurationIncidenceToBase graded f n =
          mark ≫ (r ≫ projectiveConfigurationIncidenceToBase graded f n) :=
        Category.assoc _ _ _
      _ = mark ≫ (constantCoverToBase (ULift.{u} (Fin n))
          (orderedFamilyConfigurationOver f n).left ≫ q) :=
        congrArg (mark ≫ ·) hbaseMor
      _ = (mark ≫ constantCoverToBase (ULift.{u} (Fin n))
          (orderedFamilyConfigurationOver f n).left) ≫ q :=
        Category.assoc _ _ _ |>.symm
      _ = 𝟙 _ ≫ q := congrArg (· ≫ q) hmarkBase
      _ = q := Category.id_comp _
  have hqt : q t = q a := by
    calc
      q t = projectiveConfigurationIncidenceToBase graded f n
          (r (Sigma.ι
            (fun _ : ULift.{u} (Fin n) ↦ (orderedFamilyConfigurationOver f n).left)
              (ULift.up j) t)) := by
        exact congrArg (fun h ↦ h t) hbaseMor' |>.symm
      _ = projectiveConfigurationIncidenceToBase graded f n y := by rw [hmt, hm]
      _ = q a := hy
  obtain ⟨g, hg⟩ :=
    (projectiveConfigurationQuotientMap_eq_iff_orbit graded f n t a).mp hqt
  refine ⟨g.symm j, ?_⟩
  have hmarked := projectiveConfigurationMarkedToIncidence_toProjective graded f n j
  have hjt : projectiveConfigurationIncidenceToProjective graded f n y =
      ((orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n j).left) t := by
    rw [← hm, ← hmt]
    exact congrArg (fun h ↦ h t) hmarked
  rw [hjt]
  have hcoord := configurationRightAction_coordinate f n g (g.symm j)
  have hcoordPoint := congrArg (fun h ↦ h t) hcoord
  simp only [Equiv.apply_symm_apply] at hcoordPoint
  change (((orderedFamilyConfigurationOpen f n).ι ≫
      (orderedFamilyCoordinate f n (g.symm j)).left)
        (configurationRightAction f n g t)) =
      ((orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n j).left) t at hcoordPoint
  rw [hg] at hcoordPoint
  exact hcoordPoint.symm

/-- The fiber of the universal unordered incidence subscheme at a
field-valued configuration. -/
noncomputable abbrev projectiveConfigurationFiber (n : ℕ)
    (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen graded f n).toScheme) :
    Scheme.{u} :=
  pullback (projectiveConfigurationIncidenceToBase graded f n) c

/-- The configuration fiber maps to the original projective family through
the incidence embedding. -/
noncomputable def projectiveConfigurationFiberToProjective (n : ℕ)
    (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen graded f n).toScheme) :
    projectiveConfigurationFiber graded f n c ⟶ Proj graded :=
  pullback.fst (projectiveConfigurationIncidenceToBase graded f n) c ≫
    projectiveConfigurationIncidenceToProjective graded f n

/-- The configuration fiber is over the ground field in the expected way. -/
lemma projectiveConfigurationFiberToProjective_toBase (n : ℕ)
    (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n = 𝟙 _) :
    projectiveConfigurationFiberToProjective graded f n c ≫ f =
      pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c := by
  unfold projectiveConfigurationFiberToProjective
  rw [Category.assoc, projectiveConfigurationIncidenceToProjective_toBase]
  rw [← Category.assoc, pullback.condition, Category.assoc, hc, Category.comp_id]

lemma projectiveConfigurationFiberToProjective_isFinite (n : ℕ)
    (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n = 𝟙 _) :
    IsFinite (projectiveConfigurationFiberToProjective graded f n c) := by
  have hcomp : IsFinite (projectiveConfigurationFiberToProjective graded f n c ≫ f) := by
    rw [projectiveConfigurationFiberToProjective_toBase graded f n c hc]
    infer_instance
  exact IsFinite.of_comp _ f

/-- The effective cycle represented by a field-valued unordered
configuration, with the scheme-theoretic lengths of its incidence fiber. -/
noncomputable def projectiveConfigurationCycle (n : ℕ)
    (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n = 𝟙 _) :
    EffectiveZeroCycle (Proj graded) :=
  let toK := pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c
  letI : IsFinite (projectiveConfigurationFiberToProjective graded f n c) :=
    projectiveConfigurationFiberToProjective_isFinite graded f n c hc
  pushforwardCycle (projectiveConfigurationFiberToProjective graded f n c)
    (PfaffianDescent.finiteSchemeFundamentalCycle toK)

/-- The cycle of a configuration depends only on the configuration morphism,
not on the proof that it lies over the ground field. -/
theorem projectiveConfigurationCycle_congr
    (n : ℕ)
    (c c' : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n = 𝟙 _)
    (hc' : c' ≫ projectiveConfigurationQuotientToBase graded f n = 𝟙 _)
    (h : c = c') :
    projectiveConfigurationCycle graded f n c hc =
      projectiveConfigurationCycle graded f n c' hc' := by
  subst c'
  rfl

/-- An unordered configuration of length `n` represents an effective cycle
of degree exactly `n`. -/
theorem projectiveConfigurationCycle_degree (n : ℕ)
    (c : Spec (.of K) ⟶ (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n = 𝟙 _) :
    EffectiveZeroCycle.degree f (projectiveConfigurationCycle graded f n c hc) = n := by
  let toK := pullback.snd (projectiveConfigurationIncidenceToBase graded f n) c
  let toX := projectiveConfigurationFiberToProjective graded f n c
  letI : IsFinite toX := projectiveConfigurationFiberToProjective_isFinite graded f n c hc
  change EffectiveZeroCycle.degree f
    (pushforwardCycle toX (PfaffianDescent.finiteSchemeFundamentalCycle toK)) = n
  rw [degree_pushforwardCycle]
  have hbase : toX ≫ f = toK :=
    projectiveConfigurationFiberToProjective_toBase graded f n c hc
  rw [hbase]
  exact (PfaffianDescent.finiteFiberFundamentalCycle_degree
    (projectiveConfigurationIncidenceToBase graded f n) c).trans
      (finrank_projectiveConfigurationIncidenceToBase graded f n (c (IsLocalRing.closedPoint K)))

end AllCharacteristics
