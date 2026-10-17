import PfaffianDescent.VoisinStandardOpenExtVanishing
import PfaffianDescent.VoisinPositiveTwistTriviality
import PfaffianDescent.SchemeCoverIntrinsicCohomology
/-! SOURCE ONLY / UNCHECKED. Native three-coordinate cover of P2, its
actual finite affine intersections, and explicit local positive/negative
unit frames. No global cohomology or Euler certificate is an input. -/
noncomputable section
namespace PfaffianDescent.ProjectivePlaneNative
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open ProjectiveNegativeTwist
open AllCharacteristics.HomogeneousProjective
universe u w
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "S" => MvPolynomial (Fin 3) K
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def p2Coordinate (i : Fin 3) : PS 1 :=
  ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩

/-- The three standard affine opens of projective plane. -/
def p2StandardOpen (i : Fin 3) : Scheme.Opens (Proj PS) :=
  ProjectiveSpectrum.basicOpen PS (p2Coordinate K i : S)

/-- The three coordinates generate the irrelevant ideal of the homogeneous
coordinate ring of projective plane. -/
lemma p2Coordinates_span_irrelevant :
    (HomogeneousIdeal.irrelevant PS).toIdeal ≤
      Ideal.span (Set.range fun i : Fin 3 => (p2Coordinate K i : S)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  have hpvars : p ∈ MvPolynomial.idealOfVars (Fin 3) K := by
    rw [← pow_one (MvPolynomial.idealOfVars (Fin 3) K),
      MvPolynomial.mem_pow_idealOfVars_iff]
    intro mon hmon
    have he : mon.degree = n := by
      simpa only [Finsupp.degree_apply] using
        (MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hmon).symm
    exact he ▸ hn
  change p ∈ Ideal.span (Set.range fun i : Fin 3 => MvPolynomial.X i)
  simpa only [MvPolynomial.idealOfVars] using hpvars

/-- The three standard coordinate opens cover projective plane. -/
lemma p2StandardOpen_iSup :
    ⨆ i : Fin 3, p2StandardOpen (K := K) i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  exact p2Coordinates_span_irrelevant K

/-- Multiplication by `X_i^m` is invertible after restricting to any open
contained in the standard chart `D_+(X_i)`.  This form applies directly to
every nonempty intersection in the standard Cech nerve. -/
theorem restrict_mulCoordinatePower_isIso_of_le
    (U : Scheme.Opens (Proj PS)) (i : Fin 3) (m : ℕ)
    (hU : U ≤ p2StandardOpen (K := K) i) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (mulHomogeneous PS (degreeOnePower PS (p2Coordinate K i) m) 0)) := by
  apply restrict_map_isIso_of_stalk U
  intro x
  letI : (pointIdeal PS (U.ι x)).IsPrime :=
    ProjectiveSpectrum.isPrime (U.ι x)
  have hXi : (MvPolynomial.X i : S) ∈
      (pointIdeal PS (U.ι x)).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    exact (ProjectiveSpectrum.mem_basicOpen PS
      (MvPolynomial.X i) (U.ι x)).mp (hU x.property)
  have hsx : (degreeOnePower PS (p2Coordinate K i) m : S) ∈
      (pointIdeal PS (U.ι x)).primeCompl := by
    change (MvPolynomial.X i : S) ^ m ∈
      (pointIdeal PS (U.ι x)).primeCompl
    exact Submonoid.pow_mem _ hXi m
  change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
    (mulHomogeneousPresheaf PS
      (degreeOnePower PS (p2Coordinate K i) m) 0))
  apply mulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
    PS (degreeOnePower PS (p2Coordinate K i) m) 0 (U.ι x) hsx
  exact (p2Coordinates_span_irrelevant K).trans (Ideal.span_mono (by
    rintro _ ⟨j, rfl⟩
    exact ⟨p2Coordinate K j, rfl⟩))

/-- The negative twist is trivial on any open lying inside one standard
coordinate chart. -/
def p2NegativeTwistOpenIsoUnit
    (U : Scheme.Opens (Proj PS)) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).obj (sheafOfModules PS m) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let s := degreeOnePower PS (p2Coordinate K i) m
  let f : sheafOfModules PS m ⟶ sheafOfModules PS 0 := by
    simpa using mulHomogeneous PS s 0
  letI : IsIso (R.map f) := by
    dsimp only [f, s]
    simpa using restrict_mulCoordinatePower_isIso_of_le K U i m hU
  exact asIso (R.map f) ≪≫
    (R.mapIso (unitIsoZeroTwist PS)).symm ≪≫
    Scheme.Modules.restrictUnitIso U.ι

/-- A finite intersection of projective basic opens is the basic open of
the product of their defining elements. -/
theorem projective_basicOpen_finset_inf
    {ι : Type w} (s : Finset ι) (f : ι → S) :
    AlgebraicGeometry.Proj.basicOpen PS (∏ i ∈ s, f i) =
      s.inf (fun i => AlgebraicGeometry.Proj.basicOpen PS (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert, ha, not_false_eq_true,
        Finset.inf_insert]
      rw [AlgebraicGeometry.Proj.basicOpen_mul, ih]

/-- The product of the coordinates indexing an ordered Cech intersection. -/
def p2CechDenominator (n : ℕ) (f : Fin (n + 1) → Fin 3) : S :=
  ∏ a, MvPolynomial.X (R := K) (f a)

/-- The denominator of an `n`-fold ordered intersection is homogeneous of
positive degree `n+1`. -/
theorem p2CechDenominator_mem (n : ℕ) (f : Fin (n + 1) → Fin 3) :
    p2CechDenominator (K := K) n f ∈ PS (n + 1) := by
  simpa [p2CechDenominator] using MvPolynomial.IsHomogeneous.prod
    (Finset.univ : Finset (Fin (n + 1)))
    (fun a ↦ MvPolynomial.X (R := K) (f a)) (fun _ ↦ (1 : ℕ))
    (fun a _ ↦ MvPolynomial.isHomogeneous_X K (f a))

/-- The first coordinate in a nonempty ordered intersection divides its
coordinate product. -/
theorem p2Coordinate_zero_dvd_cechDenominator
    (n : ℕ) (f : Fin (n + 1) → Fin 3) :
    MvPolynomial.X (R := K) (f 0) ∣ p2CechDenominator (K := K) n f := by
  simpa [p2CechDenominator] using
    (Finset.dvd_prod_of_mem
      (fun a : Fin (n + 1) ↦ MvPolynomial.X (R := K) (f a))
      (Finset.mem_univ (0 : Fin (n + 1))))

/-- An ordered standard-cover intersection is the basic open of the product
of its coordinate denominators. -/
theorem p2CechBasicOpen_eq_inf (n : ℕ) (f : Fin (n + 1) → Fin 3) :
    AlgebraicGeometry.Proj.basicOpen PS
        (p2CechDenominator (K := K) n f) =
      ⨅ a, p2StandardOpen (K := K) (f a) := by
  change AlgebraicGeometry.Proj.basicOpen PS
      (∏ a, MvPolynomial.X (R := K) (f a)) =
    ⨅ a, AlgebraicGeometry.Proj.basicOpen PS
      (MvPolynomial.X (R := K) (f a))
  rw [← Finset.inf_univ_eq_iInf]
  simpa using projective_basicOpen_finset_inf (K := K)
    (Finset.univ : Finset (Fin (n + 1)))
    (fun a ↦ MvPolynomial.X (R := K) (f a))

/-- Every intersection in the Cech nerve of the standard coordinate cover
of projective plane is affine. -/
theorem p2StandardOpen_cech_inter_affine
    (n : ℕ) (f : Fin (n + 1) → Fin 3) :
    AlgebraicGeometry.IsAffineOpen
      (⨅ i, p2StandardOpen (K := K) (f i)) := by
  classical
  change AlgebraicGeometry.IsAffineOpen
    (⨅ i, AlgebraicGeometry.Proj.basicOpen PS
      (MvPolynomial.X (R := K) (f i)))
  rw [← Finset.inf_univ_eq_iInf,
    ← projective_basicOpen_finset_inf (K := K)]
  have hhom : MvPolynomial.IsHomogeneous
      (∏ i : Fin (n + 1), MvPolynomial.X (R := K) (f i)) (n + 1) := by
    simpa using MvPolynomial.IsHomogeneous.prod
      (Finset.univ : Finset (Fin (n + 1)))
      (fun i => MvPolynomial.X (R := K) (f i)) (fun _ => (1 : ℕ))
      (fun i _ => MvPolynomial.isHomogeneous_X K (f i))
  exact AlgebraicGeometry.Proj.isAffineOpen_basicOpen PS
    (∏ i : Fin (n + 1), MvPolynomial.X (R := K) (f i))
    (m := n + 1) hhom (Nat.succ_pos n)


noncomputable def p2PositiveTwistOpenIsoUnit
    (U : Scheme.Opens (Proj PS)) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).obj (positiveSheafOfModules PS m) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let s := degreeOnePower PS (p2Coordinate K i) m
  let f₀ := positiveMulHomogeneous PS s 0
  let e : positiveSheafOfModules PS (0 + m) ≅
      positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
  let f : positiveSheafOfModules PS 0 ⟶ positiveSheafOfModules PS m :=
    f₀ ≫ e.hom
  have hf₀ : IsIso (R.map f₀) := by
    dsimp only [f₀, s]
    apply restrict_map_isIso_of_stalk U
    intro x
    letI : (positivePointIdeal PS (U.ι x)).IsPrime :=
      ProjectiveSpectrum.isPrime (U.ι x)
    have hXi : (MvPolynomial.X i : S) ∈
        (positivePointIdeal PS (U.ι x)).primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      exact (ProjectiveSpectrum.mem_basicOpen PS
        (MvPolynomial.X i) (U.ι x)).mp (hU x.property)
    have hsx : (degreeOnePower PS (p2Coordinate K i) m : S) ∈
        (positivePointIdeal PS (U.ι x)).primeCompl := by
      change (MvPolynomial.X i : S) ^ m ∈
        (positivePointIdeal PS (U.ι x)).primeCompl
      exact Submonoid.pow_mem _ hXi m
    change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
      (positiveMulHomogeneousPresheaf PS
        (degreeOnePower PS (p2Coordinate K i) m) 0))
    apply positiveMulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
      PS (degreeOnePower PS (p2Coordinate K i) m) 0 (U.ι x) hsx
    exact (p2Coordinates_span_irrelevant K).trans (Ideal.span_mono (by
      rintro _ ⟨j, rfl⟩
      exact ⟨p2Coordinate K j, rfl⟩))
  letI : IsIso (R.map f₀) := hf₀
  letI : IsIso (R.map f) := by
    dsimp only [f]
    rw [R.map_comp]
    infer_instance
  exact (asIso (R.map f)).symm ≪≫
    R.mapIso (positiveZeroTwistIso PS) ≪≫
    (R.mapIso (unitIsoZeroTwist PS)).symm ≪≫
    Scheme.Modules.restrictUnitIso U.ι

theorem p2_isLocallyNoetherian : IsLocallyNoetherian (Proj PS) := by
  letI : IsScalarTower K (PS 0) S := by
    constructor
    intro x y z
    change (x • (y : S)) * z = x • ((y : S) * z)
    exact smul_mul_assoc x (y : S) z
  letI : Algebra.FiniteType (PS 0) S :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (PS 0) S
  exact LocallyOfFiniteType.isLocallyNoetherian (Proj.toSpecZero PS)

/-- Actual intrinsic local acyclicity from the native positive frame on
every ordered coordinate intersection. No QC or Ext outcome premise. -/
theorem p2PositiveCechInter_sectionRepresenter_ext_one_and_two_subsingleton
    [HasExt.{u} (Proj PS).Modules] (m n : ℕ) (f : Fin (n + 1) → Fin 3) :
    let U : Scheme.Opens (Proj PS) := ⨅ i, p2StandardOpen (K := K) (f i)
    Subsingleton (Ext.{u}
      (show (Proj PS).Modules from sectionRepresenter (Proj PS).ringCatSheaf U)
      (positiveSheafOfModules PS m) 1) ∧
    Subsingleton (Ext.{u}
      (show (Proj PS).Modules from sectionRepresenter (Proj PS).ringCatSheaf U)
      (positiveSheafOfModules PS m) 2) := by
  let U : Scheme.Opens (Proj PS) := ⨅ i, p2StandardOpen (K := K) (f i)
  have hU : IsAffineOpen U := p2StandardOpen_cech_inter_affine K n f
  letI : IsLocallyNoetherian (Proj PS) := p2_isLocallyNoetherian K
  letI : IsLocallyNoetherian (U : Scheme) := inferInstance
  letI : IsAffine (U : Scheme) := hU
  letI : IsNoetherianRing Γ((U : Scheme), ⊤) :=
    IsLocallyNoetherian.component_noetherian
      ⟨⊤, isAffineOpen_top (U : Scheme)⟩
  exact sectionRepresenter_ext_one_and_two_subsingleton_of_affineOpen_of_restrictIsoUnit
    U hU (positiveSheafOfModules PS m)
    (p2PositiveTwistOpenIsoUnit K U (f 0)
      (iInf_le_of_le (0 : Fin (n + 1)) le_rfl) m)

/-- Actual intrinsic local acyclicity for all native negative twists on
the same genuine P2 coordinate intersections. -/
theorem p2NegativeCechInter_sectionRepresenter_ext_one_and_two_subsingleton
    [HasExt.{u} (Proj PS).Modules] (m n : ℕ) (f : Fin (n + 1) → Fin 3) :
    let U : Scheme.Opens (Proj PS) := ⨅ i, p2StandardOpen (K := K) (f i)
    Subsingleton (Ext.{u}
      (show (Proj PS).Modules from sectionRepresenter (Proj PS).ringCatSheaf U)
      (sheafOfModules PS m) 1) ∧
    Subsingleton (Ext.{u}
      (show (Proj PS).Modules from sectionRepresenter (Proj PS).ringCatSheaf U)
      (sheafOfModules PS m) 2) := by
  let U : Scheme.Opens (Proj PS) := ⨅ i, p2StandardOpen (K := K) (f i)
  have hU : IsAffineOpen U := p2StandardOpen_cech_inter_affine K n f
  letI : IsLocallyNoetherian (Proj PS) := p2_isLocallyNoetherian K
  letI : IsLocallyNoetherian (U : Scheme) := inferInstance
  letI : IsAffine (U : Scheme) := hU
  letI : IsNoetherianRing Γ((U : Scheme), ⊤) :=
    IsLocallyNoetherian.component_noetherian
      ⟨⊤, isAffineOpen_top (U : Scheme)⟩
  exact sectionRepresenter_ext_one_and_two_subsingleton_of_affineOpen_of_restrictIsoUnit
    U hU (sheafOfModules PS m)
    (p2NegativeTwistOpenIsoUnit K U (f 0)
      (iInf_le_of_le (0 : Fin (n + 1)) le_rfl) m)

abbrev P2CoordinateIndex := ULift.{u} (Fin 3)
def p2StandardOpenLifted (i : P2CoordinateIndex.{u}) : Scheme.Opens (Proj PS) :=
  p2StandardOpen (K := K) i.down

lemma p2StandardOpenLifted_iSup :
    ⨆ i : P2CoordinateIndex.{u}, p2StandardOpenLifted K i = ⊤ := by
  simpa [p2StandardOpenLifted, iSup_ulift] using p2StandardOpen_iSup K

/-- Actual canonical section-representer resolution of the SAME P2 cover. -/
noncomputable abbrev p2SectionRepresenterCechChain : ChainComplex (Proj PS).Modules ℕ :=
  sectionRepresenterCechChain (Proj PS).ringCatSheaf (p2StandardOpenLifted K)

end PfaffianDescent.ProjectivePlaneNative
