import AllCharacteristics.ProjectiveCoefficientMap
import AllCharacteristics.ProjectivePointCoordinates
import AllCharacteristics.CoordinateCharts
import PfaffianDescent.ProjectiveClosedImmersion
import PfaffianDescent.ProjectiveSurjectionImage
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Ambient morphisms for homogeneous projective subschemes

A homogeneous quotient induces the canonical morphism from the corresponding
projective subscheme to the ambient projective space.  This supplies the
ambient map needed to form universal hypersurface incidence loci.
-/

open AlgebraicGeometry CategoryTheory HomogeneousIdeal HomogeneousLocalization
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ R

/-- The homogeneous quotient map, regarded as a map of graded coordinate
rings. -/
noncomputable def quotientGradedRingHom (I : HomogeneousIdeal 𝒜) :
    𝒜 →+*ᵍ grading I where
  __ := Ideal.Quotient.mk I.toIdeal
  map_mem hx := ⟨_, hx, rfl⟩

/-- The quotient map takes the irrelevant ideal of the ambient projective
space onto an ideal containing the irrelevant ideal of the quotient. -/
theorem irrelevant_le_map_quotientGradedRingHom (I : HomogeneousIdeal 𝒜) :
    irrelevant (grading I) ≤
      (irrelevant 𝒜).map (quotientGradedRingHom I) := by
  change (irrelevant (grading I)).toIdeal ≤
    ((irrelevant 𝒜).map (quotientGradedRingHom I)).toIdeal
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn x hx
  change x ∈ grading I n at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact Ideal.mem_map_of_mem (quotientGradedRingHom I)
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn hy)

/-- The canonical morphism from the projective scheme of a homogeneous ideal
to the ambient projective space. -/
noncomputable def quotientProjMap (I : HomogeneousIdeal 𝒜) :
    scheme I ⟶ Proj 𝒜 :=
  Proj.map (quotientGradedRingHom I) (irrelevant_le_map_quotientGradedRingHom I)

/-- The structure morphism of the ambient projective space of a homogeneous
polynomial ring. -/
noncomputable def ambientToBase : Proj 𝒜 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))

private lemma ambientChart_toBase (s : MvPolynomial σ R) {d : ℕ}
    (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    Proj.awayι 𝒜 s hs hd ≫ ambientToBase =
      Spec.map (CommRingCat.ofHom
        (AllCharacteristics.GradedChart.baseMap 𝒜 (z := s))) := by
  change Proj.awayι 𝒜 s hs hd ≫
    (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The coordinate basic opens cover ordinary ambient projective space. -/
noncomputable def ambientCoordinateOpenCover : (Proj 𝒜).AffineOpenCover := by
  have hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ R)) := by
    rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    intro n hn x hx
    change x ∈ MvPolynomial.idealOfVars σ R
    rw [← pow_one (MvPolynomial.idealOfVars σ R), MvPolynomial.mem_pow_idealOfVars_iff]
    intro m hm
    have he : m.degree = n := by
      simpa only [Finsupp.degree_apply] using
        (MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hx hm).symm
    exact he ▸ hn
  exact Proj.affineOpenCoverOfIrrelevantLESpan 𝒜 MvPolynomial.X
    (MvPolynomial.isHomogeneous_X R) (fun _ => by decide) hspan

/-- The canonical closed immersion of a homogeneous projective subscheme is
a morphism over the coefficient ring. -/
theorem quotientProjMap_toBase (I : HomogeneousIdeal 𝒜) :
    quotientProjMap I ≫ ambientToBase = toBase I := by
  let F := quotientGradedRingHom I
  let hF := irrelevant_le_map_quotientGradedRingHom I
  let bA : Proj 𝒜 ⟶ Spec (.of R) := ambientToBase
  let bI : Proj (grading I) ⟶ Spec (.of R) := toBase I
  change Proj.map F hF ≫ bA = bI
  apply (Proj.mapAffineOpenCover F hF).openCover.hom_ext
  intro s
  change (Σ d : PNat, 𝒜 d) at s
  obtain ⟨⟨d, hd⟩, s, hs⟩ := s
  change s ∈ 𝒜 d at hs
  change Proj.awayι (grading I) (F s) (F.2 hs) hd ≫
    (Proj.map F hF ≫ bA) =
    Proj.awayι (grading I) (F s) (F.2 hs) hd ≫ bI
  have hbA : Proj.awayι 𝒜 s hs hd ≫ bA =
      Spec.map (CommRingCat.ofHom
        (AllCharacteristics.GradedChart.baseMap 𝒜 (z := s))) :=
    ambientChart_toBase s hs hd
  have hbI : Proj.awayι (grading I) (F s) (F.2 hs) hd ≫ bI =
      Spec.map (CommRingCat.ofHom
        (AllCharacteristics.GradedChart.baseMap (grading I) (z := F s))) := by
    change Proj.awayι (grading I) (F s) (F.2 hs) hd ≫
      (Proj.toSpecZero (grading I) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (grading I 0)))) = _
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  rw [← Category.assoc, Proj.awayι_comp_map, Category.assoc, hbA, hbI,
    ← Spec.map_comp]
  congr 1
  exact hs

/-- The homogeneous quotient map is surjective. -/
theorem quotientGradedRingHom_surjective (I : HomogeneousIdeal 𝒜) :
    Function.Surjective (quotientGradedRingHom I) :=
  Ideal.Quotient.mk_surjective

/-- The homogeneous quotient map preserves the classes of all projective
coordinates. -/
theorem quotientGradedRingHom_coordinate (I : HomogeneousIdeal 𝒜) (j : σ) :
    quotientGradedRingHom I (MvPolynomial.X j) = coordinate I j := by
  change Ideal.Quotient.mk I.toIdeal (MvPolynomial.X j) =
    Ideal.Quotient.mk I.toIdeal (MvPolynomial.X j)
  rfl

/-- A homogeneous projective subscheme is closed in its ambient projective
space. -/
instance quotientProjMap_isClosedImmersion (I : HomogeneousIdeal 𝒜) :
    IsClosedImmersion (quotientProjMap I) := by
  exact PfaffianDescent.projectiveMap_closedImmersion_of_surjective
    (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)

/-- The image of the canonical projective quotient is exactly the homogeneous
zero locus of its defining ideal. -/
theorem quotientProjMap_mem_range_iff
    (I : HomogeneousIdeal 𝒜) (x : Proj 𝒜) :
    x ∈ Set.range (quotientProjMap I) ↔ I.toIdeal ≤ x.asHomogeneousIdeal.toIdeal := by
  change x ∈ Set.range (Proj.map (quotientGradedRingHom I)
    (irrelevant_le_map_quotientGradedRingHom I)) ↔ _
  rw [PfaffianDescent.projectiveMap_mem_range_iff
    (quotientGradedRingHom I) (quotientGradedRingHom_surjective I)]
  change RingHom.ker (Ideal.Quotient.mk I.toIdeal) ≤ _ ↔ _
  rw [Ideal.mk_ker]

/-- The topological image of the canonical projective quotient is the
projective zero locus of the homogeneous ideal. -/
theorem range_quotientProjMap
    (I : HomogeneousIdeal 𝒜) :
    Set.range (quotientProjMap I) = ProjectiveSpectrum.zeroLocus 𝒜 I.toIdeal := by
  ext x
  rw [quotientProjMap_mem_range_iff]
  exact (ProjectiveSpectrum.mem_zeroLocus 𝒜 x I.toIdeal).symm

/-- A relevant homogeneous prime ideal is recovered from its projective zero
locus by taking the homogeneous vanishing ideal. -/
theorem vanishingIdeal_zeroLocus_eq_of_prime_relevant
    (I : HomogeneousIdeal 𝒜) (hprime : I.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ I) :
    ProjectiveSpectrum.vanishingIdeal
      (ProjectiveSpectrum.zeroLocus 𝒜 I.toIdeal) = I := by
  let x : ProjectiveSpectrum 𝒜 := ⟨I, hprime, hrelevant⟩
  apply le_antisymm
  · intro f hf
    have hx : x ∈ ProjectiveSpectrum.zeroLocus 𝒜 I.toIdeal := by
      rw [ProjectiveSpectrum.mem_zeroLocus]
      exact fun y hy => hy
    have hfx : f ∈ x.asHomogeneousIdeal :=
      (ProjectiveSpectrum.mem_vanishingIdeal _ _).mp hf x hx
    exact hfx
  · exact ProjectiveSpectrum.homogeneousIdeal_le_vanishingIdeal_zeroLocus 𝒜 I

/-- The homogeneous ideal of functions vanishing on the underlying closed
subset of a projective immersion. -/
noncomputable def closedImmersionVanishingIdeal {X : Scheme.{u}} (i : X ⟶ Proj 𝒜) :
    HomogeneousIdeal 𝒜 :=
  ProjectiveSpectrum.vanishingIdeal
    (Set.range (fun x => (i x : ProjectiveSpectrum 𝒜)))

/-- An embedded projective scheme identified with the Proj of a relevant
homogeneous prime has precisely that homogeneous vanishing ideal. -/
theorem closedImmersionVanishingIdeal_eq_of_iso_quotient
    (I : HomogeneousIdeal 𝒜) (hprime : I.toIdeal.IsPrime)
    (hrelevant : ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ I)
    {X : Scheme.{u}} (i : X ⟶ Proj 𝒜)
    (e : X ≅ scheme I)
    (he : e.hom ≫ quotientProjMap I = i) :
    closedImmersionVanishingIdeal i = I := by
  unfold closedImmersionVanishingIdeal
  change ProjectiveSpectrum.vanishingIdeal
    (Set.range (fun x => (i x : ProjectiveSpectrum 𝒜))) = I
  have hrange : Set.range (fun x => (i x : ProjectiveSpectrum 𝒜)) =
      Set.range (fun x => ((quotientProjMap I) x : ProjectiveSpectrum 𝒜)) := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx⟩
      refine ⟨e.hom x, ?_⟩
      rw [← hx]
      change (e.hom ≫ quotientProjMap I) x = i x
      rw [he]
    · rintro y ⟨z, hz⟩
      refine ⟨e.inv z, ?_⟩
      rw [← hz]
      change i (e.inv z) = (quotientProjMap I) z
      rw [← he]
      simp
  have hquotientRange : Set.range (fun x =>
      ((quotientProjMap I) x : ProjectiveSpectrum 𝒜)) =
      ProjectiveSpectrum.zeroLocus 𝒜 I.toIdeal := by
    exact range_quotientProjMap I
  exact (congrArg ProjectiveSpectrum.vanishingIdeal hrange).trans
    ((congrArg ProjectiveSpectrum.vanishingIdeal hquotientRange).trans
      (vanishingIdeal_zeroLocus_eq_of_prime_relevant I hprime hrelevant))

/-- A closed immersion into a projective scheme is recovered as the zero
locus of its homogeneous vanishing ideal at the level of underlying spaces. -/
theorem zeroLocus_closedImmersionVanishingIdeal
    {X : Scheme.{u}} (i : X ⟶ Proj 𝒜) [IsClosedImmersion i] :
    ProjectiveSpectrum.zeroLocus 𝒜 (closedImmersionVanishingIdeal i).toIdeal = Set.range i := by
  change ProjectiveSpectrum.zeroLocus 𝒜
    (ProjectiveSpectrum.vanishingIdeal
      (Set.range (fun x => (i x : ProjectiveSpectrum 𝒜))) : Set _) = _
  rw [ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have hclosed : IsClosed (Set.range (fun x => (i x : ProjectiveSpectrum 𝒜))) := by
    exact i.isClosedEmbedding.isClosed_range
  exact hclosed.closure_eq

/-- The homogeneous vanishing ideal of any projective closed subset is
radical: it is an intersection of homogeneous prime ideals. -/
theorem closedImmersionVanishingIdeal_isRadical
    {X : Scheme.{u}} (i : X ⟶ Proj 𝒜) :
    (closedImmersionVanishingIdeal i).toIdeal.IsRadical := by
  unfold closedImmersionVanishingIdeal ProjectiveSpectrum.vanishingIdeal
  rw [HomogeneousIdeal.toIdeal_iInf]
  apply Ideal.isRadical_iInf
  intro x
  rw [HomogeneousIdeal.toIdeal_iInf]
  apply Ideal.isRadical_iInf
  intro _
  exact x.isPrime.isRadical

/-- A homogeneous ideal whose underlying polynomial ideal is radical defines
a reduced projective scheme. -/
theorem scheme_isReduced_of_isRadical
    (I : HomogeneousIdeal 𝒜) (hI : I.toIdeal.IsRadical) :
    IsReduced (scheme I) := by
  rw [IsReduced.iff_of_openCover (scheme I) (coordinateOpenCover I).openCover]
  intro j
  change IsReduced (Spec (.of (ChartRing I j)))
  haveI : _root_.IsReduced (CoordinateRing I) :=
    (Ideal.isRadical_iff_quotient_reduced I.toIdeal).mp hI
  haveI : _root_.IsReduced (Localization (.powers (coordinate I j))) := inferInstance
  letI : _root_.IsReduced (ChartRing I j) := isReduced_of_injective
    (algebraMap (ChartRing I j) (Localization (.powers (coordinate I j))))
    (HomogeneousLocalization.val_injective _)
  infer_instance

/-- The Proj scheme defined by the homogeneous vanishing ideal of a projective
closed subset is reduced. -/
theorem scheme_closedImmersionVanishingIdeal_isReduced
    {X : Scheme.{u}} (i : X ⟶ Proj 𝒜) :
    IsReduced (scheme (closedImmersionVanishingIdeal i)) :=
  scheme_isReduced_of_isRadical _ (closedImmersionVanishingIdeal_isRadical i)

/-- The canonical ambient morphism of a projective hypersurface. -/
noncomputable def hypersurfaceToAmbient (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) : hypersurface p hp ⟶ Proj 𝒜 :=
  quotientProjMap (equationIdeal p hp)

/-- A projective hypersurface is closed in its ambient projective space. -/
instance hypersurfaceToAmbient_isClosedImmersion (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) :
    IsClosedImmersion (hypersurfaceToAmbient p hp) := by
  change IsClosedImmersion (quotientProjMap (equationIdeal p hp))
  infer_instance


/-- A projective morphism factoring through a hypersurface annihilates the
ideal sheaf of that hypersurface in the ambient projective space. -/
theorem hypersurface_ker_le_of_factor
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    {X : Scheme.{u}} (q : X ⟶ hypersurface p hp)
    (i : X ⟶ Proj 𝒜)
    (hfac : q ≫ hypersurfaceToAmbient p hp = i) :
    (hypersurfaceToAmbient p hp).ker ≤ i.ker := by
  rw [← hfac]
  exact q.le_ker_comp (hypersurfaceToAmbient p hp)

/-- The affine map from an ambient coordinate chart to the corresponding
chart of a projective hypersurface. -/
noncomputable def hypersurfaceAmbientChartMap (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) (j : σ) :
    Away 𝒜 (MvPolynomial.X j) →+* ChartRing (equationIdeal p hp) j :=
  gradedAwayMapOfEq (quotientGradedRingHom (equationIdeal p hp))
    (MvPolynomial.X j) (coordinate (equationIdeal p hp) j)
    (quotientGradedRingHom_coordinate (equationIdeal p hp) j)

/-- Every normalized function on a hypersurface chart is the restriction of
an ambient normalized function. -/
theorem hypersurfaceAmbientChartMap_surjective
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (j : σ) :
    Function.Surjective (hypersurfaceAmbientChartMap p hp j) := by
  intro y
  let I := equationIdeal p hp
  obtain ⟨n, q, hq, rfl⟩ :=
    Away.mk_surjective (grading I) (coordinate_mem I j) y
  obtain ⟨r, hr, hrq⟩ := hq
  let hx : MvPolynomial.X j ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X R j
  refine ⟨Away.mk 𝒜 hx n r hr, ?_⟩
  change (gradedAwayMapOfEq (quotientGradedRingHom I)
      (MvPolynomial.X j) (coordinate I j)
      (quotientGradedRingHom_coordinate I j)) (Away.mk 𝒜 hx n r hr) = _
  rw [gradedAwayMapOfEq_mk (quotientGradedRingHom I)
    (MvPolynomial.X j) (coordinate I j)
    (quotientGradedRingHom_coordinate I j) hx (coordinate_mem I j) n r hr]
  change Away.mk (grading I) (coordinate_mem I j) n
    ((Ideal.Quotient.mk I.toIdeal) r) _ = Away.mk (grading I) (coordinate_mem I j) n q _
  congr 1

/-- The ambient chart map preserves all normalized homogeneous coordinates. -/
theorem hypersurfaceAmbientChartMap_coordinate (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) (j i : σ) :
    hypersurfaceAmbientChartMap p hp j
      (AllCharacteristics.GradedChart.normalized 𝒜
        (MvPolynomial.isHomogeneous_X R j) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i)) =
      chartCoordinate (equationIdeal p hp) j i := by
  let hxj : MvPolynomial.X j ∈ 𝒜 1 := by
    exact MvPolynomial.isHomogeneous_X R j
  let hxi : MvPolynomial.X i ∈ 𝒜 1 := by
    exact MvPolynomial.isHomogeneous_X R i
  let hyj : coordinate (equationIdeal p hp) j ∈ grading (equationIdeal p hp) 1 :=
    coordinate_mem (equationIdeal p hp) j
  let hyi : coordinate (equationIdeal p hp) i ∈ grading (equationIdeal p hp) 1 :=
    coordinate_mem (equationIdeal p hp) i
  unfold hypersurfaceAmbientChartMap chartCoordinate AllCharacteristics.GradedChart.normalized
  change (gradedAwayMapOfEq (quotientGradedRingHom (equationIdeal p hp))
    (MvPolynomial.X j) (coordinate (equationIdeal p hp) j)
    (quotientGradedRingHom_coordinate (equationIdeal p hp) j))
      (Away.mk 𝒜 hxj 1 (MvPolynomial.X i) (by simpa only [one_smul] using hxi)) =
    Away.mk (grading (equationIdeal p hp)) hyj 1
      (coordinate (equationIdeal p hp) i) (by simpa only [one_smul] using hyi)
  rw [gradedAwayMapOfEq_mk (quotientGradedRingHom (equationIdeal p hp))
    (MvPolynomial.X j) (coordinate (equationIdeal p hp) j)
    (quotientGradedRingHom_coordinate (equationIdeal p hp) j) hxj hyj 1
    (MvPolynomial.X i) hxi]
  cases quotientGradedRingHom_coordinate (equationIdeal p hp) i
  rfl

/-- On every ambient degree-one chart, the normalized defining equation of a
hypersurface vanishes in that hypersurface's chart ring. -/
theorem hypersurfaceAmbientChartMap_equation_eq_zero
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (j : σ) :
    hypersurfaceAmbientChartMap p hp j
      (Away.mk 𝒜 (MvPolynomial.isHomogeneous_X R j) d p (by simpa using hp)) = 0 := by
  let hxj : MvPolynomial.X j ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X R j
  let hyj : coordinate (equationIdeal p hp) j ∈ grading (equationIdeal p hp) 1 :=
    coordinate_mem (equationIdeal p hp) j
  unfold hypersurfaceAmbientChartMap
  change (gradedAwayMapOfEq (quotientGradedRingHom (equationIdeal p hp))
    (MvPolynomial.X j) (coordinate (equationIdeal p hp) j)
    (quotientGradedRingHom_coordinate (equationIdeal p hp) j))
    (Away.mk 𝒜 hxj d p (by simpa using hp)) = 0
  rw [gradedAwayMapOfEq_mk (quotientGradedRingHom (equationIdeal p hp))
    (MvPolynomial.X j) (coordinate (equationIdeal p hp) j)
    (quotientGradedRingHom_coordinate (equationIdeal p hp) j) hxj hyj d p
    (by simpa using hp)]
  have hpzero : quotientGradedRingHom (equationIdeal p hp) p = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton p))
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_zero]
  rw [hpzero]
  exact Localization.mk_zero _

/-- The normalized equation generates an ideal contained in the kernel of
the affine-chart restriction map. The reverse inclusion is the local
principal-ideal presentation needed for the Cartier divisor. -/
theorem normalizedEquationIdeal_le_hypersurfaceAmbientChartMap_ker
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (j : σ) :
    Ideal.span ({Away.mk 𝒜 (MvPolynomial.isHomogeneous_X R j) d p
      (by simpa using hp)} : Set (Away 𝒜 (MvPolynomial.X j))) ≤
      RingHom.ker (hypersurfaceAmbientChartMap p hp j) := by
  apply Ideal.span_le.mpr
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact hypersurfaceAmbientChartMap_equation_eq_zero p hp j

/-- An ambient kernel-ideal inclusion into a homogeneous projective quotient
forces the normalized hypersurface equation to vanish on each coordinate
chart of that quotient. -/
theorem away_mk_eq_zero_of_hypersurface_ker_le_quotientProjMap_coordinate
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (I : HomogeneousIdeal 𝒜)
    (hker : (hypersurfaceToAmbient p hp).ker ≤ (quotientProjMap I).ker)
    (j : σ) :
    Away.mk (grading I) (coordinate_mem I j) d (Ideal.Quotient.mk I.toIdeal p)
      (by simpa using polynomial_class_mem_grading I p hp) = 0 := by
  let U : (Proj 𝒜).affineOpens :=
    ⟨Proj.basicOpen 𝒜 (MvPolynomial.X j),
      Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j) (by decide)⟩
  let a := Away.mk 𝒜 (MvPolynomial.isHomogeneous_X R j) d p (by simpa using hp)
  have hmem : Proj.awayToSection 𝒜 (MvPolynomial.X j) a ∈
      (hypersurfaceToAmbient p hp).ker.ideal U := by
    rw [(hypersurfaceToAmbient p hp).ker_apply U, RingHom.mem_ker]
    change (hypersurfaceToAmbient p hp).appLE
      (Proj.basicOpen 𝒜 (MvPolynomial.X j))
      (Proj.basicOpen (grading (equationIdeal p hp))
        (coordinate (equationIdeal p hp) j)) (by rfl)
      (Proj.awayToSection 𝒜 (MvPolynomial.X j) a) = 0
    have hmapzero : Away.map (quotientGradedRingHom (equationIdeal p hp))
        (MvPolynomial.X j) a = 0 := by
      change hypersurfaceAmbientChartMap p hp j a = 0
      exact hypersurfaceAmbientChartMap_equation_eq_zero p hp j
    have he := congrArg (fun k => k a)
      (Proj.awayToSection_comp_appLE
        (quotientGradedRingHom (equationIdeal p hp))
        (irrelevant_le_map_quotientGradedRingHom (equationIdeal p hp))
        (MvPolynomial.isHomogeneous_X R j))
    change (hypersurfaceToAmbient p hp).appLE
      (Proj.basicOpen 𝒜 (MvPolynomial.X j))
      (Proj.basicOpen (grading (equationIdeal p hp))
        (coordinate (equationIdeal p hp) j)) (by rfl)
      (Proj.awayToSection 𝒜 (MvPolynomial.X j) a) =
      Proj.awayToSection (grading (equationIdeal p hp))
        (coordinate (equationIdeal p hp) j)
        (Away.map (quotientGradedRingHom (equationIdeal p hp))
          (MvPolynomial.X j) a) at he
    rw [hmapzero] at he
    calc
      _ = Proj.awayToSection (grading (equationIdeal p hp))
          (coordinate (equationIdeal p hp) j) 0 := he
      _ = 0 := map_zero _
  have hmem' : Proj.awayToSection 𝒜 (MvPolynomial.X j) a ∈
      (quotientProjMap I).ker.ideal U := hker U hmem
  have hzero : (quotientProjMap I).app U
      (Proj.awayToSection 𝒜 (MvPolynomial.X j) a) = 0 := by
    rw [(quotientProjMap I).ker_apply U, RingHom.mem_ker] at hmem'
    exact hmem'
  have hzeroLE : (quotientProjMap I).appLE
      (Proj.basicOpen 𝒜 (MvPolynomial.X j))
      (Proj.basicOpen (grading I) (coordinate I j)) (by rfl)
      (Proj.awayToSection 𝒜 (MvPolynomial.X j) a) = 0 := by
    change (quotientProjMap I).app U
      (Proj.awayToSection 𝒜 (MvPolynomial.X j) a) = 0
    exact hzero
  have he := congrArg (fun k => k a)
    (Proj.awayToSection_comp_appLE (quotientGradedRingHom I)
      (irrelevant_le_map_quotientGradedRingHom I)
      (MvPolynomial.isHomogeneous_X R j))
  change (quotientProjMap I).appLE
    (Proj.basicOpen 𝒜 (MvPolynomial.X j))
    (Proj.basicOpen (grading I) (coordinate I j)) (by rfl)
    (Proj.awayToSection 𝒜 (MvPolynomial.X j) a) =
    Proj.awayToSection (grading I) (coordinate I j)
      (Away.map (quotientGradedRingHom I) (MvPolynomial.X j) a) at he
  have hsection : Proj.awayToSection (grading I) (coordinate I j)
      (Away.map (quotientGradedRingHom I) (MvPolynomial.X j) a) = 0 := by
    calc
      _ = (quotientProjMap I).appLE
        (Proj.basicOpen 𝒜 (MvPolynomial.X j))
        (Proj.basicOpen (grading I) (coordinate I j)) (by rfl)
        (Proj.awayToSection 𝒜 (MvPolynomial.X j) a) := he.symm
      _ = 0 := hzeroLE
  haveI : IsIso (Proj.awayToSection (grading I) (coordinate I j)) := by
    exact (Proj.basicOpenIsoAway (grading I) (coordinate I j)
      (coordinate_mem I j) (by decide)).isIso_hom
  have hmapzero : Away.map (quotientGradedRingHom I) (MvPolynomial.X j) a = 0 :=
    (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      (Proj.awayToSection (grading I) (coordinate I j))).1).mp hsection
  change Away.map (quotientGradedRingHom I) (MvPolynomial.X j) a = 0
  exact hmapzero

/-- The same kernel-ideal argument works on the affine chart of every
degree-one homogeneous form, not only the coordinate charts. -/
theorem away_mk_eq_zero_of_hypersurface_ker_le_quotientProjMap
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (I : HomogeneousIdeal 𝒜) (z : MvPolynomial σ R) (hz : z ∈ 𝒜 1)
    (hker : (hypersurfaceToAmbient p hp).ker ≤ (quotientProjMap I).ker) :
    Away.mk (grading I) ((quotientGradedRingHom I).map_mem hz) d
      (Ideal.Quotient.mk I.toIdeal p)
      (by simpa using polynomial_class_mem_grading I p hp) = 0 := by
  let U : (Proj 𝒜).affineOpens :=
    ⟨Proj.basicOpen 𝒜 z, Proj.isAffineOpen_basicOpen 𝒜 z hz (by decide)⟩
  let a := Away.mk 𝒜 hz d p (by simpa using hp)
  have hmem : Proj.awayToSection 𝒜 z a ∈
      (hypersurfaceToAmbient p hp).ker.ideal U := by
    rw [(hypersurfaceToAmbient p hp).ker_apply U, RingHom.mem_ker]
    change (hypersurfaceToAmbient p hp).appLE
      (Proj.basicOpen 𝒜 z)
      (Proj.basicOpen (grading (equationIdeal p hp))
        ((quotientGradedRingHom (equationIdeal p hp)) z)) (by rfl)
      (Proj.awayToSection 𝒜 z a) = 0
    have hmapzero : Away.map (quotientGradedRingHom (equationIdeal p hp)) z a = 0 := by
      unfold a
      rw [Away.map_mk]
      have hpzero : quotientGradedRingHom (equationIdeal p hp) p = 0 := by
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_singleton p))
      apply HomogeneousLocalization.val_injective
      simp only [Away.val_mk, HomogeneousLocalization.val_zero]
      rw [hpzero]
      exact Localization.mk_zero _
    have he := congrArg (fun k => k a)
      (Proj.awayToSection_comp_appLE
        (quotientGradedRingHom (equationIdeal p hp))
        (irrelevant_le_map_quotientGradedRingHom (equationIdeal p hp)) hz)
    change (hypersurfaceToAmbient p hp).appLE
      (Proj.basicOpen 𝒜 z)
      (Proj.basicOpen (grading (equationIdeal p hp))
        ((quotientGradedRingHom (equationIdeal p hp)) z)) (by rfl)
      (Proj.awayToSection 𝒜 z a) =
      Proj.awayToSection (grading (equationIdeal p hp))
        ((quotientGradedRingHom (equationIdeal p hp)) z)
        (Away.map (quotientGradedRingHom (equationIdeal p hp)) z a) at he
    rw [hmapzero] at he
    calc
      _ = Proj.awayToSection (grading (equationIdeal p hp))
          ((quotientGradedRingHom (equationIdeal p hp)) z) 0 := he
      _ = 0 := map_zero _
  have hmem' : Proj.awayToSection 𝒜 z a ∈
      (quotientProjMap I).ker.ideal U := hker U hmem
  have hzero : (quotientProjMap I).app U
      (Proj.awayToSection 𝒜 z a) = 0 := by
    rw [(quotientProjMap I).ker_apply U, RingHom.mem_ker] at hmem'
    exact hmem'
  have hzeroLE : (quotientProjMap I).appLE
      (Proj.basicOpen 𝒜 z)
      (Proj.basicOpen (grading I) ((quotientGradedRingHom I) z)) (by rfl)
      (Proj.awayToSection 𝒜 z a) = 0 := by
    change (quotientProjMap I).app U (Proj.awayToSection 𝒜 z a) = 0
    exact hzero
  have he := congrArg (fun k => k a)
    (Proj.awayToSection_comp_appLE (quotientGradedRingHom I)
      (irrelevant_le_map_quotientGradedRingHom I) hz)
  change (quotientProjMap I).appLE
    (Proj.basicOpen 𝒜 z)
    (Proj.basicOpen (grading I) ((quotientGradedRingHom I) z)) (by rfl)
    (Proj.awayToSection 𝒜 z a) =
    Proj.awayToSection (grading I) ((quotientGradedRingHom I) z)
      (Away.map (quotientGradedRingHom I) z a) at he
  have hsection : Proj.awayToSection (grading I) ((quotientGradedRingHom I) z)
      (Away.map (quotientGradedRingHom I) z a) = 0 := by
    calc
      _ = (quotientProjMap I).appLE
        (Proj.basicOpen 𝒜 z)
        (Proj.basicOpen (grading I) ((quotientGradedRingHom I) z)) (by rfl)
        (Proj.awayToSection 𝒜 z a) := he.symm
      _ = 0 := hzeroLE
  haveI : IsIso (Proj.awayToSection (grading I) ((quotientGradedRingHom I) z)) := by
    exact (Proj.basicOpenIsoAway (grading I) ((quotientGradedRingHom I) z)
      ((quotientGradedRingHom I).map_mem hz) (by decide)).isIso_hom
  have hmapzero : Away.map (quotientGradedRingHom I) z a = 0 :=
    (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      (Proj.awayToSection (grading I) ((quotientGradedRingHom I) z))).1).mp hsection
  change Away.map (quotientGradedRingHom I) z a = 0
  exact hmapzero

/-- On each actual affine coordinate chart, the ambient hypersurface map is
the spectrum of `hypersurfaceAmbientChartMap`. -/
theorem chartι_comp_hypersurfaceToAmbient (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) (j : σ) :
    chartι (equationIdeal p hp) j ≫ hypersurfaceToAmbient p hp =
      Spec.map (CommRingCat.ofHom (hypersurfaceAmbientChartMap p hp j)) ≫
        Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < 1) := by
  change Proj.awayι (grading (equationIdeal p hp))
      (coordinate (equationIdeal p hp) j) (coordinate_mem (equationIdeal p hp) j)
      (by decide : 0 < 1) ≫
        Proj.map (quotientGradedRingHom (equationIdeal p hp))
          (irrelevant_le_map_quotientGradedRingHom (equationIdeal p hp)) = _
  exact awayι_comp_map_of_eq (quotientGradedRingHom (equationIdeal p hp))
    (irrelevant_le_map_quotientGradedRingHom (equationIdeal p hp))
    (MvPolynomial.X j) (coordinate (equationIdeal p hp) j)
    (quotientGradedRingHom_coordinate (equationIdeal p hp) j)
    (by decide : 0 < 1) (MvPolynomial.isHomogeneous_X R j)
    (coordinate_mem (equationIdeal p hp) j)

/-- If the ambient image of a field-valued hypersurface point lies in a
specified coordinate chart, the point itself has a chart presentation in the
corresponding hypersurface chart. -/
theorem exists_chart_hom_of_hypersurface_point_of_mem_ambient_coordinate
    {k : Type u} [Field k] (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) (f : R →+* k)
    (q : Spec (.of k) ⟶ hypersurface p hp)
    (hq : q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom f))
    (j : σ)
    (hj : (q ≫ hypersurfaceToAmbient p hp) (IsLocalRing.closedPoint k) ∈ Set.range
      (Proj.awayι 𝒜 (MvPolynomial.X j)
        (by exact MvPolynomial.isHomogeneous_X R j)
        (by decide : 0 < 1))) :
    ∃ g : ChartRing (equationIdeal p hp) j →+* k,
      g.comp (chartBaseMap (equationIdeal p hp) j) = f ∧
        Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) j = q := by
  let hX : MvPolynomial.X j ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X R j
  have hjBasic : (hypersurfaceToAmbient p hp) (q (IsLocalRing.closedPoint k)) ∈
      Proj.basicOpen 𝒜 (MvPolynomial.X j) := by
    change (hypersurfaceToAmbient p hp) (q (IsLocalRing.closedPoint k)) ∈
      Set.range (Proj.awayι 𝒜 (MvPolynomial.X j) hX (by decide : 0 < 1)) at hj
    exact (Proj.opensRange_awayι 𝒜 (MvPolynomial.X j) hX (by decide : 0 < 1)) ▸ hj
  let q' : Spec (.of k) ⟶ scheme (equationIdeal p hp) := q
  have hq' : q' ≫ toBase (equationIdeal p hp) = Spec.map (CommRingCat.ofHom f) := hq
  have hjPreimage : q' (IsLocalRing.closedPoint k) ∈
      (Proj.map (quotientGradedRingHom (equationIdeal p hp))
        (irrelevant_le_map_quotientGradedRingHom (equationIdeal p hp))) ⁻¹ᵁ
          Proj.basicOpen 𝒜 (MvPolynomial.X j) := by
    change (hypersurfaceToAmbient p hp) (q (IsLocalRing.closedPoint k)) ∈
      Proj.basicOpen 𝒜 (MvPolynomial.X j)
    exact hjBasic
  have hjSourceBasic : q' (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (grading (equationIdeal p hp))
        (coordinate (equationIdeal p hp) j) := by
    change q' (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (grading (equationIdeal p hp))
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal (MvPolynomial.X j))
    change q' (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (grading (equationIdeal p hp))
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal (MvPolynomial.X j)) at hjPreimage
    exact hjPreimage
  have hjSource : q' (IsLocalRing.closedPoint k) ∈
      Set.range (chartι (equationIdeal p hp) j) := by
    change q' (IsLocalRing.closedPoint k) ∈
      (Proj.awayι (grading (equationIdeal p hp))
        (coordinate (equationIdeal p hp) j)
        (coordinate_mem (equationIdeal p hp) j) (by decide : 0 < 1)).opensRange
    exact (Proj.opensRange_awayι (grading (equationIdeal p hp))
      (coordinate (equationIdeal p hp) j)
      (coordinate_mem (equationIdeal p hp) j) (by decide : 0 < 1)).symm ▸ hjSourceBasic
  simpa only [q'] using
    (exists_chart_hom_eq_of_point_of_mem_range (equationIdeal p hp) f q' hq' j hjSource)

/-- In the specified ambient coordinate chart, a field-valued hypersurface
point gives normalized coordinates on which its defining equation vanishes. -/
theorem exists_chart_hom_and_eval_eq_zero_of_hypersurface_point_of_mem_ambient_coordinate
    {k : Type u} [Field k] (p : MvPolynomial σ R) {d : ℕ}
    (hp : p.IsHomogeneous d) (f : R →+* k)
    (q : Spec (.of k) ⟶ hypersurface p hp)
    (hq : q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom f))
    (j : σ)
    (hj : (q ≫ hypersurfaceToAmbient p hp) (IsLocalRing.closedPoint k) ∈ Set.range
      (Proj.awayι 𝒜 (MvPolynomial.X j)
        (by exact MvPolynomial.isHomogeneous_X R j)
        (by decide : 0 < 1))) :
    ∃ g : ChartRing (equationIdeal p hp) j →+* k,
      g.comp (chartBaseMap (equationIdeal p hp) j) = f ∧
        Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) j = q ∧
          p.eval₂ f (fun i ↦ g (chartCoordinate (equationIdeal p hp) j i)) = 0 := by
  obtain ⟨g, hg, hqg⟩ :=
    exists_chart_hom_of_hypersurface_point_of_mem_ambient_coordinate p hp f q hq j hj
  refine ⟨g, hg, hqg, ?_⟩
  have hzero := congrArg g
    (eval₂_chartCoordinate_eq_zero (equationIdeal p hp) j p hp
      (Ideal.subset_span (Set.mem_singleton p)))
  rw [MvPolynomial.hom_eval₂, hg, map_zero] at hzero
  exact hzero

section CoefficientChange

variable {S : Type u} [CommRing S]
local notation "𝓑" => MvPolynomial.homogeneousSubmodule σ S

/-- Coefficient change as a map of the homogeneous coordinate rings of
ambient projective spaces. -/
noncomputable def ambientCoefficientGradedRingHom (f : R →+* S) : 𝒜 →+*ᵍ 𝓑 where
  __ := MvPolynomial.map f
  map_mem hx := hx.map f

/-- The ambient coefficient map fixes the homogeneous coordinate variables. -/
theorem ambientCoefficientGradedRingHom_X (f : R →+* S) (j : σ) :
    ambientCoefficientGradedRingHom f (MvPolynomial.X j) = MvPolynomial.X j := by
  change MvPolynomial.map f (MvPolynomial.X j) = MvPolynomial.X j
  rw [MvPolynomial.map_X]

/-- Coefficient change maps the ambient irrelevant ideal onto an ideal
containing the target irrelevant ideal, because it fixes every projective
coordinate. -/
theorem irrelevant_le_map_ambientCoefficientGradedRingHom (f : R →+* S) :
    irrelevant 𝓑 ≤ (irrelevant 𝒜).map (ambientCoefficientGradedRingHom f) := by
  change (irrelevant 𝓑).toIdeal ≤
    ((irrelevant 𝒜).map (ambientCoefficientGradedRingHom f)).toIdeal
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn x hx
  change x.IsHomogeneous n at hx
  have hxvars : x ∈ MvPolynomial.idealOfVars σ S := by
    rw [← pow_one (MvPolynomial.idealOfVars σ S), MvPolynomial.mem_pow_idealOfVars_iff]
    intro m hm
    have he : m.degree = n := by
      simpa only [Finsupp.degree_apply] using
        (MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hx hm).symm
    exact he ▸ hn
  have hle : MvPolynomial.idealOfVars σ S ≤
      ((irrelevant 𝒜).map (ambientCoefficientGradedRingHom f)).toIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    rw [← MvPolynomial.map_X (f := f) j]
    exact Ideal.mem_map_of_mem (ambientCoefficientGradedRingHom f)
      (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 (by decide : 0 < 1)
        (MvPolynomial.isHomogeneous_X R j))
  exact hle hxvars

/-- The morphism of ambient projective spaces induced by coefficient change. -/
noncomputable def ambientCoefficientMap (f : R →+* S) : Proj 𝓑 ⟶ Proj 𝒜 :=
  Proj.map (ambientCoefficientGradedRingHom f)
    (irrelevant_le_map_ambientCoefficientGradedRingHom f)

/-- The map on ordinary ambient projective coordinate charts induced by a
coefficient homomorphism. -/
noncomputable def ambientCoefficientChartMap (f : R →+* S) (j : σ) :
    Away 𝒜 (MvPolynomial.X j) →+* Away 𝓑 (MvPolynomial.X j) :=
  gradedAwayMapOfEq (ambientCoefficientGradedRingHom f)
    (MvPolynomial.X j) (MvPolynomial.X j) (ambientCoefficientGradedRingHom_X f j)

/-- Coefficient change on an ambient projective chart commutes with the
coefficient maps from the two base rings. -/
theorem ambientCoefficientChartMap_baseMap (f : R →+* S) (j : σ) (r : R) :
    ambientCoefficientChartMap f j
      (AllCharacteristics.GradedChart.baseMap 𝒜 (z := MvPolynomial.X j) r) =
    AllCharacteristics.GradedChart.baseMap 𝓑 (z := MvPolynomial.X j) (f r) := by
  let hx : MvPolynomial.X j ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X R j
  let hy : MvPolynomial.X j ∈ 𝓑 1 := MvPolynomial.isHomogeneous_X S j
  have hc : MvPolynomial.C r ∈ 𝒜 (0 • 1) := by
    simpa using MvPolynomial.isHomogeneous_C (σ := σ) r
  have hm := gradedAwayMapOfEq_mk (ambientCoefficientGradedRingHom f)
    (MvPolynomial.X j) (MvPolynomial.X j) (ambientCoefficientGradedRingHom_X f j)
    hx hy 0 (MvPolynomial.C r) hc
  change gradedAwayMapOfEq (ambientCoefficientGradedRingHom f)
      (MvPolynomial.X j) (MvPolynomial.X j) (ambientCoefficientGradedRingHom_X f j)
      (Away.mk 𝒜 hx 0 (MvPolynomial.C r) hc) =
    Away.mk 𝓑 hy 0 (MvPolynomial.C (f r))
      (by simpa using (MvPolynomial.isHomogeneous_C (σ := σ) (f r)))
  have hC : ambientCoefficientGradedRingHom (σ := σ) f
      (MvPolynomial.C r : MvPolynomial σ R) =
      (MvPolynomial.C (f r) : MvPolynomial σ S) := by
    change MvPolynomial.map f (MvPolynomial.C r) = _
    exact MvPolynomial.map_C f r
  simpa only [hC] using hm

/-- Coefficient change preserves the normalized coordinate functions on an
ordinary ambient projective chart. -/
theorem ambientCoefficientChartMap_coordinate (f : R →+* S) (j i : σ) :
    ambientCoefficientChartMap f j
      (AllCharacteristics.GradedChart.normalized 𝒜
        (MvPolynomial.isHomogeneous_X R j) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i)) =
      AllCharacteristics.GradedChart.normalized 𝓑
        (MvPolynomial.isHomogeneous_X S j) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X S i) := by
  let hxj : MvPolynomial.X j ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X R j
  let hxi : MvPolynomial.X i ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X R i
  let hyj : MvPolynomial.X j ∈ 𝓑 1 := MvPolynomial.isHomogeneous_X S j
  let hyi : MvPolynomial.X i ∈ 𝓑 1 := MvPolynomial.isHomogeneous_X S i
  unfold ambientCoefficientChartMap AllCharacteristics.GradedChart.normalized
  change (gradedAwayMapOfEq (ambientCoefficientGradedRingHom f)
    (MvPolynomial.X j) (MvPolynomial.X j) (ambientCoefficientGradedRingHom_X f j))
      (Away.mk 𝒜 hxj 1 (MvPolynomial.X i) (by simpa only [one_smul] using hxi)) =
    Away.mk 𝓑 hyj 1 (MvPolynomial.X i) (by simpa only [one_smul] using hyi)
  rw [gradedAwayMapOfEq_mk (ambientCoefficientGradedRingHom f)
    (MvPolynomial.X j) (MvPolynomial.X j) (ambientCoefficientGradedRingHom_X f j) hxj hyj 1
    (MvPolynomial.X i) hxi]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk]
  congr 1
  exact ambientCoefficientGradedRingHom_X f i

/-- On an ambient coordinate chart, coefficient change is represented by
`ambientCoefficientChartMap`. -/
theorem awayι_comp_ambientCoefficientMap (f : R →+* S) (j : σ) :
    Proj.awayι 𝓑 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X S j)
      (by decide : 0 < 1) ≫ ambientCoefficientMap f =
      Spec.map (CommRingCat.ofHom (ambientCoefficientChartMap f j)) ≫
        Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < 1) := by
  exact awayι_comp_map_of_eq (ambientCoefficientGradedRingHom f)
    (irrelevant_le_map_ambientCoefficientGradedRingHom f)
    (MvPolynomial.X j) (MvPolynomial.X j) (ambientCoefficientGradedRingHom_X f j)
    (by decide : 0 < 1) (MvPolynomial.isHomogeneous_X R j)
    (MvPolynomial.isHomogeneous_X S j)

/-- The ambient coefficient-change morphism is over the original coefficient
ring. -/
theorem ambientCoefficientMap_toBase (f : R →+* S) :
    ambientCoefficientMap (σ := σ) f ≫ ambientToBase (R := R) (σ := σ) =
      ambientToBase (R := S) (σ := σ) ≫
        Spec.map (CommRingCat.ofHom f) := by
  apply (ambientCoordinateOpenCover (R := S) (σ := σ)).openCover.hom_ext
  intro j
  change σ at j
  change Proj.awayι 𝓑 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X S j)
      (by decide : 0 < 1) ≫
        (ambientCoefficientMap (σ := σ) f ≫ ambientToBase (R := R) (σ := σ)) =
    Proj.awayι 𝓑 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X S j)
      (by decide : 0 < 1) ≫
        (ambientToBase (R := S) (σ := σ) ≫ Spec.map (CommRingCat.ofHom f))
  have hbR := ambientChart_toBase (R := R) (σ := σ)
    (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j) (by decide : 0 < 1)
  have hbS := ambientChart_toBase (R := S) (σ := σ)
    (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X S j) (by decide : 0 < 1)
  rw [← Category.assoc, awayι_comp_ambientCoefficientMap,
    Category.assoc, hbR, ← Category.assoc, hbS,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact ambientCoefficientChartMap_baseMap f j r

/-- The inverse image of an ordinary ambient coordinate chart under
coefficient change is the corresponding coordinate chart after change of
coefficients. -/
theorem ambientCoefficientMap_preimage_basicOpen (f : R →+* S) (j : σ) :
    ambientCoefficientMap (σ := σ) f ⁻¹ᵁ
        Proj.basicOpen 𝒜 (MvPolynomial.X j) =
      Proj.basicOpen 𝓑 (MvPolynomial.X j) := by
  change Proj.map (ambientCoefficientGradedRingHom f)
      (irrelevant_le_map_ambientCoefficientGradedRingHom f) ⁻¹ᵁ
        Proj.basicOpen 𝒜 (MvPolynomial.X j) =
      Proj.basicOpen 𝓑 (MvPolynomial.X j)
  rw [Proj.map_preimage_basicOpen, ambientCoefficientGradedRingHom_X]

/-- Each ambient projective coordinate chart is the exact pullback of the
corresponding chart along coefficient change. -/
theorem isPullback_ambientCoefficientMap_chart (f : R →+* S) (j : σ) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (ambientCoefficientChartMap f j)))
      (Proj.awayι 𝓑 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X S j)
        (by decide : 0 < 1))
      (Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
        (by decide : 0 < 1))
      (ambientCoefficientMap f) := by
  letI : IsOpenImmersion (Proj.awayι 𝒜 (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X R j) (by decide : 0 < 1)) := by
    unfold Proj.awayι
    exact IsOpenImmersion.comp _ _
  letI : IsOpenImmersion (Proj.awayι 𝓑 (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X S j) (by decide : 0 < 1)) := by
    unfold Proj.awayι
    exact IsOpenImmersion.comp _ _
  apply IsOpenImmersion.isPullback _ _ _ _
    (awayι_comp_ambientCoefficientMap f j)
  let hx : MvPolynomial.X j ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X R j
  let hy : MvPolynomial.X j ∈ 𝓑 1 := MvPolynomial.isHomogeneous_X S j
  have hr :
      (Proj.awayι 𝒜 (MvPolynomial.X j) hx Nat.zero_lt_one).opensRange =
        Proj.basicOpen 𝒜 (MvPolynomial.X j) :=
    Proj.opensRange_awayι 𝒜 (MvPolynomial.X j) hx Nat.zero_lt_one
  have hs :
      (Proj.awayι 𝓑 (MvPolynomial.X j) hy Nat.zero_lt_one).opensRange =
        Proj.basicOpen 𝓑 (MvPolynomial.X j) :=
    Proj.opensRange_awayι 𝓑 (MvPolynomial.X j) hy Nat.zero_lt_one
  exact (congrArg (fun U => ambientCoefficientMap f ⁻¹ᵁ U) hr).trans
    ((ambientCoefficientMap_preimage_basicOpen f j).trans hs.symm)

/-- Two ordinary ambient-chart homomorphisms are equal when they induce the
same projective point in that chart. -/
theorem ambientCoefficientChartMap_eq_of_projective_eq {A : Type u} [CommRing A]
    (j : σ) (g h : Away 𝒜 (MvPolynomial.X j) →+* A)
    (hgh : Spec.map (CommRingCat.ofHom g) ≫
      Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
        (by decide : 0 < 1) =
      Spec.map (CommRingCat.ofHom h) ≫
        Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < 1)) : g = h := by
  letI : IsOpenImmersion (Proj.awayι 𝒜 (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X R j) (by decide : 0 < 1)) := by
    unfold Proj.awayι
    exact IsOpenImmersion.comp _ _
  letI : Mono (Proj.awayι 𝒜 (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X R j) (by decide : 0 < 1)) :=
    IsOpenImmersion.mono _
  have hs : Spec.map (CommRingCat.ofHom g) = Spec.map (CommRingCat.ofHom h) :=
    (cancel_mono (Proj.awayι 𝒜 (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one)).mp hgh
  have hc : CommRingCat.ofHom g = CommRingCat.ofHom h := Spec.map_injective hs
  exact congrArg CommRingCat.Hom.hom hc

/-- A hypersurface chart followed by coefficient change is represented by the
composite of its ambient chart map and the ambient coefficient chart map. -/
theorem chartι_comp_hypersurfaceToAmbient_comp_ambientCoefficientMap
    (f : R →+* S) (p : MvPolynomial σ S) {d : ℕ} (hp : p.IsHomogeneous d)
    (j : σ) :
    chartι (equationIdeal p hp) j ≫ hypersurfaceToAmbient p hp ≫
      ambientCoefficientMap f =
      Spec.map (CommRingCat.ofHom
        ((hypersurfaceAmbientChartMap p hp j).comp (ambientCoefficientChartMap f j))) ≫
        Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < 1) := by
  change chartι (equationIdeal p hp) j ≫
      (quotientProjMap (equationIdeal p hp) ≫ ambientCoefficientMap f) = _
  have hchart : chartι (equationIdeal p hp) j ≫
      quotientProjMap (equationIdeal p hp) =
      Spec.map (CommRingCat.ofHom (hypersurfaceAmbientChartMap p hp j)) ≫
        Proj.awayι 𝓑 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X S j)
          (by decide : 0 < 1) := by
    exact chartι_comp_hypersurfaceToAmbient p hp j
  rw [← Category.assoc, hchart,
    Category.assoc, awayι_comp_ambientCoefficientMap,
    ← Category.assoc, ← Spec.map_comp]
  rfl

/-- If the ambient image of a hypersurface-chart point after coefficient
change agrees with a raw ambient-chart point, then the two chart-ring maps
are equal. -/
theorem hypersurfaceAmbientCoefficientChartMap_eq_of_projective_eq
    {A : Type u} [CommRing A] (f : R →+* S)
    (p : MvPolynomial σ S) {d : ℕ} (hp : p.IsHomogeneous d) (j : σ)
    (g : ChartRing (equationIdeal p hp) j →+* A)
    (h : Away 𝒜 (MvPolynomial.X j) →+* A)
    (hgh : Spec.map (CommRingCat.ofHom g) ≫
      (chartι (equationIdeal p hp) j ≫ hypersurfaceToAmbient p hp ≫
        ambientCoefficientMap f) =
      Spec.map (CommRingCat.ofHom h) ≫
        Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < 1)) :
    g.comp ((hypersurfaceAmbientChartMap p hp j).comp
      (ambientCoefficientChartMap f j)) = h := by
  apply ambientCoefficientChartMap_eq_of_projective_eq j
  calc
    Spec.map (CommRingCat.ofHom
        (g.comp ((hypersurfaceAmbientChartMap p hp j).comp
          (ambientCoefficientChartMap f j)))) ≫
        Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < 1) =
      Spec.map (CommRingCat.ofHom g) ≫
        (Spec.map (CommRingCat.ofHom
          ((hypersurfaceAmbientChartMap p hp j).comp
            (ambientCoefficientChartMap f j))) ≫
          Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
            (by decide : 0 < 1)) := by
        rw [← Category.assoc, ← Spec.map_comp]
        rfl
    _ = Spec.map (CommRingCat.ofHom g) ≫
        (chartι (equationIdeal p hp) j ≫ hypersurfaceToAmbient p hp ≫
          ambientCoefficientMap f) := by
        rw [chartι_comp_hypersurfaceToAmbient_comp_ambientCoefficientMap]
    _ = Spec.map (CommRingCat.ofHom h) ≫
        Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < 1) := hgh

/-- Under the preceding ambient-chart comparison, normalized hypersurface
coordinates agree with the corresponding raw ambient-chart coordinates. -/
theorem hypersurfaceChartCoordinate_eq_of_ambient_eq
    {A : Type u} [CommRing A] (f : R →+* S)
    (p : MvPolynomial σ S) {d : ℕ} (hp : p.IsHomogeneous d) (j i : σ)
    (g : ChartRing (equationIdeal p hp) j →+* A)
    (h : Away 𝒜 (MvPolynomial.X j) →+* A)
    (hgh : Spec.map (CommRingCat.ofHom g) ≫
      (chartι (equationIdeal p hp) j ≫ hypersurfaceToAmbient p hp ≫
        ambientCoefficientMap f) =
      Spec.map (CommRingCat.ofHom h) ≫
        Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < 1)) :
    g (chartCoordinate (equationIdeal p hp) j i) =
      h (AllCharacteristics.GradedChart.normalized 𝒜
        (MvPolynomial.isHomogeneous_X R j) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i)) := by
  have hmaps := hypersurfaceAmbientCoefficientChartMap_eq_of_projective_eq
    f p hp j g h hgh
  have hi := congrArg (fun φ ↦ φ
    (AllCharacteristics.GradedChart.normalized 𝒜
      (MvPolynomial.isHomogeneous_X R j) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i))) hmaps
  change g (hypersurfaceAmbientChartMap p hp j
    (ambientCoefficientChartMap f j
      (AllCharacteristics.GradedChart.normalized 𝒜
        (MvPolynomial.isHomogeneous_X R j) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i)))) = _ at hi
  rw [ambientCoefficientChartMap_coordinate,
    hypersurfaceAmbientChartMap_coordinate] at hi
  exact hi

/-- A field-valued hypersurface point whose coefficient-changed ambient image
has a raw chart presentation admits the corresponding hypersurface chart
presentation.  Its normalized coordinates agree with the raw chart
coordinates, and its equation vanishes on them. -/
theorem exists_chart_hom_and_coordinates_eq_of_ambient_eq
    {A : Type u} [Field A] (a : R →+* S) (p : MvPolynomial σ S)
    {d : ℕ} (hp : p.IsHomogeneous d) (b : S →+* A)
    (q : Spec (.of A) ⟶ hypersurface p hp)
    (hq : q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom b))
    (j : σ) (h : Away 𝒜 (MvPolynomial.X j) →+* A)
    (hambient : q ≫ hypersurfaceToAmbient p hp ≫ ambientCoefficientMap a =
      Spec.map (CommRingCat.ofHom h) ≫
        Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < 1)) :
    ∃ g : ChartRing (equationIdeal p hp) j →+* A,
      g.comp (chartBaseMap (equationIdeal p hp) j) = b ∧
        Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) j = q ∧
          (∀ i : σ, g (chartCoordinate (equationIdeal p hp) j i) =
            h (AllCharacteristics.GradedChart.normalized 𝒜
              (MvPolynomial.isHomogeneous_X R j) (MvPolynomial.X i)
              (MvPolynomial.isHomogeneous_X R i))) ∧
          p.eval₂ b (fun i ↦ g (chartCoordinate (equationIdeal p hp) j i)) = 0 := by
  have hraw : (q ≫ hypersurfaceToAmbient p hp ≫ ambientCoefficientMap a)
      (IsLocalRing.closedPoint A) ∈ Set.range
        (Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < 1)) := by
    rw [hambient]
    exact ⟨(Spec.map (CommRingCat.ofHom h)) (IsLocalRing.closedPoint A), rfl⟩
  have hbasicR : (q ≫ hypersurfaceToAmbient p hp ≫ ambientCoefficientMap a)
      (IsLocalRing.closedPoint A) ∈ Proj.basicOpen 𝒜 (MvPolynomial.X j) := by
    exact (Proj.opensRange_awayι 𝒜 (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X R j) (by decide : 0 < 1)) ▸ hraw
  have hbasicS : (q ≫ hypersurfaceToAmbient p hp)
      (IsLocalRing.closedPoint A) ∈
        Proj.basicOpen 𝓑 (MvPolynomial.X j) := by
    change (q ≫ hypersurfaceToAmbient p hp) (IsLocalRing.closedPoint A) ∈
      ambientCoefficientMap a ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) at hbasicR
    change (q ≫ hypersurfaceToAmbient p hp) (IsLocalRing.closedPoint A) ∈
      Proj.map (ambientCoefficientGradedRingHom a)
        (irrelevant_le_map_ambientCoefficientGradedRingHom a) ⁻¹ᵁ
          Proj.basicOpen 𝒜 (MvPolynomial.X j) at hbasicR
    rw [Proj.map_preimage_basicOpen] at hbasicR
    change (q ≫ hypersurfaceToAmbient p hp) (IsLocalRing.closedPoint A) ∈
      Proj.basicOpen 𝓑 (MvPolynomial.map a (MvPolynomial.X j)) at hbasicR
    rw [MvPolynomial.map_X] at hbasicR
    exact hbasicR
  letI : IsOpenImmersion (Proj.awayι 𝓑 (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X S j) Nat.zero_lt_one) := by
    unfold Proj.awayι
    exact IsOpenImmersion.comp _ _
  have hj : (q ≫ hypersurfaceToAmbient p hp) (IsLocalRing.closedPoint A) ∈
      Set.range (Proj.awayι 𝓑 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X S j) Nat.zero_lt_one) := by
    change (q ≫ hypersurfaceToAmbient p hp) (IsLocalRing.closedPoint A) ∈
      (Proj.awayι 𝓑 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X S j) Nat.zero_lt_one).opensRange
    exact (Proj.opensRange_awayι 𝓑 (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X S j) Nat.zero_lt_one).symm ▸ hbasicS
  obtain ⟨g, hgbase, hgpoint, hzero⟩ :=
    exists_chart_hom_and_eval_eq_zero_of_hypersurface_point_of_mem_ambient_coordinate
      p hp b q hq j hj
  have hgh : Spec.map (CommRingCat.ofHom g) ≫
      (chartι (equationIdeal p hp) j ≫ hypersurfaceToAmbient p hp ≫
        ambientCoefficientMap a) =
      Spec.map (CommRingCat.ofHom h) ≫
        Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < 1) := by
    calc
      Spec.map (CommRingCat.ofHom g) ≫
          (chartι (equationIdeal p hp) j ≫ hypersurfaceToAmbient p hp ≫
            ambientCoefficientMap a) =
        (Spec.map (CommRingCat.ofHom g) ≫ chartι (equationIdeal p hp) j) ≫
          (hypersurfaceToAmbient p hp ≫ ambientCoefficientMap a) :=
            (Category.assoc _ _ _).symm
      _ = q ≫ hypersurfaceToAmbient p hp ≫ ambientCoefficientMap a := by
        rw [hgpoint]
        rfl
      _ = Spec.map (CommRingCat.ofHom h) ≫
        Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < 1) := hambient
  refine ⟨g, hgbase, hgpoint, ?_, hzero⟩
  intro i
  exact hypersurfaceChartCoordinate_eq_of_ambient_eq a p hp j i g h hgh

/-- In the ambient-chart situation above, the specialized equation vanishes
directly on the raw ambient-chart coordinates. -/
theorem aeval_map_eq_zero_of_ambient_eq
    {A : Type u} [Field A] (a : R →+* S) (p : MvPolynomial σ S)
    {d : ℕ} (hp : p.IsHomogeneous d) (b : S →+* A)
    (q : Spec (.of A) ⟶ hypersurface p hp)
    (hq : q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom b))
    (j : σ) (h : Away 𝒜 (MvPolynomial.X j) →+* A)
    (hambient : q ≫ hypersurfaceToAmbient p hp ≫ ambientCoefficientMap a =
      Spec.map (CommRingCat.ofHom h) ≫
        Proj.awayι 𝒜 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          (by decide : 0 < 1)) :
    MvPolynomial.aeval
        (fun i ↦ h (AllCharacteristics.GradedChart.normalized 𝒜
          (MvPolynomial.isHomogeneous_X R j) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X R i)))
        (p.map b) = 0 := by
  obtain ⟨g, hgbase, hgpoint, hcoordinates, hzero⟩ :=
    exists_chart_hom_and_coordinates_eq_of_ambient_eq a p hp b q hq j h hambient
  have hcoordinates' :
      (fun i ↦ g (chartCoordinate (equationIdeal p hp) j i)) =
        fun i ↦ h (AllCharacteristics.GradedChart.normalized 𝒜
          (MvPolynomial.isHomogeneous_X R j) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X R i)) := by
    funext i
    exact hcoordinates i
  rw [hcoordinates'] at hzero
  rw [MvPolynomial.aeval_def]
  simpa using hzero

/-- Coefficient change preserves each ambient projective coordinate chart. -/
theorem ambientCoefficientMap_preimage_coordinate (f : R →+* S) (j : σ) :
    ambientCoefficientMap (σ := σ) f ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) =
      Proj.basicOpen 𝓑 (MvPolynomial.X j) := by
  change Proj.map (ambientCoefficientGradedRingHom f)
      (irrelevant_le_map_ambientCoefficientGradedRingHom f) ⁻¹ᵁ
        Proj.basicOpen 𝒜 (MvPolynomial.X j) = _
  rw [Proj.map_preimage_basicOpen]
  change Proj.basicOpen 𝓑 (MvPolynomial.map f (MvPolynomial.X j)) = _
  rw [MvPolynomial.map_X]

/-- Equal admissible graded maps induce equal ambient projective morphisms. -/
theorem ambientProjMap_congr (φ ψ : 𝒜 →+*ᵍ 𝓑)
    (hφ : irrelevant 𝓑 ≤ (irrelevant 𝒜).map φ)
    (hψ : irrelevant 𝓑 ≤ (irrelevant 𝒜).map ψ)
    (h : φ = ψ) : Proj.map φ hφ = Proj.map ψ hψ := by
  subst ψ
  rfl

/-- Taking a homogeneous quotient commutes with changing the coefficient
ring, as a map of graded coordinate rings. -/
theorem gradedCoefficientMap_comp_quotientGradedRingHom
    (f : R →+* S) (I : HomogeneousIdeal 𝒜) (J : HomogeneousIdeal 𝓑)
    (h : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal) :
    (gradedCoefficientMap f I J h).comp (quotientGradedRingHom I) =
      (quotientGradedRingHom J).comp (ambientCoefficientGradedRingHom f) := by
  apply GradedRingHom.ext
  intro x
  change coordinateCoefficientMap f I J h (Ideal.Quotient.mk I.toIdeal x) =
    Ideal.Quotient.mk J.toIdeal (MvPolynomial.map f x)
  rw [coordinateCoefficientMap_mk]

/-- The ambient morphism of a homogeneous subscheme is natural under
coefficient change. -/
theorem projectiveCoefficientMap_comp_quotientProjMap
    (f : R →+* S) (I : HomogeneousIdeal 𝒜) (J : HomogeneousIdeal 𝓑)
    (h : I.toIdeal.map (MvPolynomial.map f) = J.toIdeal) :
    projectiveCoefficientMap f I J h ≫ quotientProjMap I =
      quotientProjMap J ≫ ambientCoefficientMap f := by
  change Proj.map (gradedCoefficientMap f I J h)
      (irrelevant_le_map_gradedCoefficientMap f I J h) ≫
        Proj.map (quotientGradedRingHom I)
          (irrelevant_le_map_quotientGradedRingHom I) =
      Proj.map (quotientGradedRingHom J)
          (irrelevant_le_map_quotientGradedRingHom J) ≫
        Proj.map (ambientCoefficientGradedRingHom f)
          (irrelevant_le_map_ambientCoefficientGradedRingHom f)
  calc
    _ = Proj.map ((gradedCoefficientMap f I J h).comp (quotientGradedRingHom I))
        (HomogeneousIdeal.irrelevant_le_map_comp
          (irrelevant_le_map_quotientGradedRingHom I)
          (irrelevant_le_map_gradedCoefficientMap f I J h)) :=
      (Proj.map_comp (quotientGradedRingHom I) (gradedCoefficientMap f I J h)
        (irrelevant_le_map_quotientGradedRingHom I)
        (irrelevant_le_map_gradedCoefficientMap f I J h)).symm
    _ = Proj.map ((quotientGradedRingHom J).comp (ambientCoefficientGradedRingHom f))
        (HomogeneousIdeal.irrelevant_le_map_comp
          (irrelevant_le_map_ambientCoefficientGradedRingHom f)
          (irrelevant_le_map_quotientGradedRingHom J)) := by
      have hgraded := gradedCoefficientMap_comp_quotientGradedRingHom f I J h
      cases hgraded
      rfl
    _ = _ := Proj.map_comp (ambientCoefficientGradedRingHom f) (quotientGradedRingHom J)
      (irrelevant_le_map_ambientCoefficientGradedRingHom f)
      (irrelevant_le_map_quotientGradedRingHom J)

section Composition

variable {T : Type u} [CommRing T]
local notation "𝓒" => MvPolynomial.homogeneousSubmodule σ T

/-- Ambient coefficient maps compose as the underlying coefficient maps do. -/
theorem ambientCoefficientGradedRingHom_comp (f : R →+* S) (g : S →+* T) :
    (ambientCoefficientGradedRingHom (σ := σ) g).comp
      (ambientCoefficientGradedRingHom (σ := σ) f) =
        ambientCoefficientGradedRingHom (σ := σ) (g.comp f) := by
  apply GradedRingHom.ext
  intro x
  change MvPolynomial.map g (MvPolynomial.map f x) = MvPolynomial.map (g.comp f) x
  exact MvPolynomial.map_map f g x

/-- The projective-space morphisms induced by two coefficient changes compose
to the morphism induced by their composite. -/
theorem ambientCoefficientMap_comp (f : R →+* S) (g : S →+* T) :
    ambientCoefficientMap (σ := σ) g ≫ ambientCoefficientMap (σ := σ) f =
      ambientCoefficientMap (σ := σ) (g.comp f) := by
  change Proj.map (ambientCoefficientGradedRingHom (σ := σ) g)
      (irrelevant_le_map_ambientCoefficientGradedRingHom (σ := σ) g) ≫
        Proj.map (ambientCoefficientGradedRingHom (σ := σ) f)
          (irrelevant_le_map_ambientCoefficientGradedRingHom (σ := σ) f) =
      Proj.map (ambientCoefficientGradedRingHom (σ := σ) (g.comp f))
        (irrelevant_le_map_ambientCoefficientGradedRingHom (σ := σ) (g.comp f))
  calc
    _ = Proj.map ((ambientCoefficientGradedRingHom (σ := σ) g).comp
        (ambientCoefficientGradedRingHom (σ := σ) f))
        (HomogeneousIdeal.irrelevant_le_map_comp
          (irrelevant_le_map_ambientCoefficientGradedRingHom (σ := σ) f)
          (irrelevant_le_map_ambientCoefficientGradedRingHom (σ := σ) g)) :=
      (Proj.map_comp (ambientCoefficientGradedRingHom (σ := σ) f)
        (ambientCoefficientGradedRingHom (σ := σ) g)
        (irrelevant_le_map_ambientCoefficientGradedRingHom (σ := σ) f)
        (irrelevant_le_map_ambientCoefficientGradedRingHom (σ := σ) g)).symm
    _ = _ := by
      exact ambientProjMap_congr _ _
        (HomogeneousIdeal.irrelevant_le_map_comp
          (irrelevant_le_map_ambientCoefficientGradedRingHom (σ := σ) f)
          (irrelevant_le_map_ambientCoefficientGradedRingHom (σ := σ) g))
        (irrelevant_le_map_ambientCoefficientGradedRingHom (σ := σ) (g.comp f))
        (ambientCoefficientGradedRingHom_comp (σ := σ) f g)

end Composition

end CoefficientChange

end HomogeneousProjective
end AllCharacteristics
