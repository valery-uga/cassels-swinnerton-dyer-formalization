import PfaffianDescent.PointAdaptedAffineCover
import PfaffianDescent.SectionRepresenterKoszulOverlapMaps
import PfaffianDescent.SectionRepresenterCechVertexMap

/-!
# First Koszul lifts of the adapted cover's vertex boundary

The distinguished vertex maps identically into the parameter representer;
all other vertices map to zero. Each signed overlap boundary lifts through
the last Koszul differential, using the geometric unit ideal off the point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace PfaffianDescent.PointAdaptedAffineCover

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

variable {X : Scheme.{u}}

/-- The actual vertex map used for the point-resolution comparison. -/
def vertexMap (U : X.Opens) (x : X) :
    ∀ i : Index X x, sectionRepresenter X.ringCatSheaf (opens U x i) ⟶
      sectionRepresenter X.ringCatSheaf U
  | none => 𝟙 _
  | some _ => 0

/-- The ordered categorical overlap. -/
abbrev pairOpen (U : X.Opens) (x : X) (i j : Index X x) : X.Opens :=
  ∏ᶜ ![opens U x i, opens U x j]

/-- The signed vertex boundary on this ordered overlap. -/
def pairBoundary (U : X.Opens) (x : X) (i j : Index X x) :
    sectionRepresenter X.ringCatSheaf (pairOpen U x i j) ⟶
      sectionRepresenter X.ringCatSheaf U :=
  (sectionRepresenterFunctor X.ringCatSheaf).map
      (Pi.π ![opens U x i, opens U x j] 1) ≫ vertexMap U x j -
    (sectionRepresenterFunctor X.ringCatSheaf).map
      (Pi.π ![opens U x i, opens U x j] 0) ≫ vertexMap U x i

theorem pairOpen_eq_inf (U : X.Opens) (x : X) (i j : Index X x) :
    pairOpen U x i j = opens U x i ⊓ opens U x j := by
  apply le_antisymm
  · exact le_inf (Pi.π ![opens U x i, opens U x j] 0).le
      (Pi.π ![opens U x i, opens U x j] 1).le
  · exact (Pi.lift (fun k : Fin 2 => homOfLE (by
      fin_cases k
      · exact inf_le_left
      · exact inf_le_right))).le

set_option backward.isDefEq.respectTransparency false in
/-- On any affine subopen away from the point, the inclusion into the
parameter representer lifts through the last Koszul differential. -/
theorem exists_inclusion_lift
    (U : X.Opens) (x : X) (q f : Γ(X, U))
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ U) (hxW : x ∉ W) :
    ∃ v : sectionRepresenter X.ringCatSheaf W ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U,
      v ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
        (sectionRepresenterFunctor X.ringCatSheaf).map (homOfLE hWU) := by
  obtain ⟨v, hv⟩ := exists_sectionRepresenterKoszulOverlapLift_away_point
    U x q f haway W hW hWU hxW 1
  refine ⟨v, ?_⟩
  simpa only [sectionRepresenterOverlapScalar, sectionRepresenterScalarEndomorphism_one,
    Category.id_comp] using hv

set_option backward.isDefEq.respectTransparency false in
/-- Every signed vertex boundary on the actual adapted cover has a sheaf
Koszul lift. There is no first-lift hypothesis in this result. -/
theorem exists_pairBoundary_lift
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (q f : Γ(X, U))
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤)
    (i j : Index X x) :
    ∃ v : sectionRepresenter X.ringCatSheaf (pairOpen U x i j) ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U,
      v ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f = pairBoundary U x i j := by
  have hW : IsAffineOpen (pairOpen U x i j) := by
    rw [pairOpen_eq_inf]
    exact isAffineOpen_inter U hU x i j
  cases i with
  | none =>
    cases j with
    | none =>
      refine ⟨0, ?_⟩
      have hπ : Pi.π ![U, U] 1 = Pi.π ![U, U] 0 := Subsingleton.elim _ _
      simp only [pairBoundary, opens_none, vertexMap, Category.comp_id, hπ,
        sub_self, zero_comp]
    | some V =>
      have hWU : pairOpen U x none (some V) ≤ U :=
        (Pi.π ![U, V.val] 0).le
      have hxW : x ∉ pairOpen U x none (some V) :=
        fun h => V.prop.2 ((Pi.π ![U, V.val] 1).le h)
      obtain ⟨v, hv⟩ := exists_inclusion_lift U x q f haway _ hW hWU hxW
      refine ⟨-v, ?_⟩
      rw [Preadditive.neg_comp, hv]
      have hπ : homOfLE hWU = Pi.π ![U, V.val] 0 := Subsingleton.elim _ _
      simp only [pairBoundary, vertexMap, comp_zero, Category.comp_id, zero_sub,
        opens_none, opens_some, hπ]
      let k : sectionRepresenter X.ringCatSheaf (pairOpen U x none (some V)) ⟶
          sectionRepresenter X.ringCatSheaf U :=
        (sectionRepresenterFunctor X.ringCatSheaf).map (Pi.π ![U, V.val] 0)
      change -k = -(k ≫ 𝟙 _)
      exact congrArg Neg.neg (Category.comp_id k).symm
  | some V =>
    cases j with
    | none =>
      have hWU : pairOpen U x (some V) none ≤ U :=
        (Pi.π ![V.val, U] 1).le
      have hxW : x ∉ pairOpen U x (some V) none :=
        fun h => V.prop.2 ((Pi.π ![V.val, U] 0).le h)
      obtain ⟨v, hv⟩ := exists_inclusion_lift U x q f haway _ hW hWU hxW
      refine ⟨v, ?_⟩
      rw [hv]
      have hπ : homOfLE hWU = Pi.π ![V.val, U] 1 := Subsingleton.elim _ _
      simp only [pairBoundary, vertexMap, comp_zero, Category.comp_id, sub_zero,
        opens_none, opens_some, hπ]
      let k : sectionRepresenter X.ringCatSheaf (pairOpen U x (some V) none) ⟶
          sectionRepresenter X.ringCatSheaf U :=
        (sectionRepresenterFunctor X.ringCatSheaf).map (Pi.π ![V.val, U] 1)
      change k = k ≫ 𝟙 _
      exact (Category.comp_id k).symm
    | some W =>
      refine ⟨0, ?_⟩
      simp only [pairBoundary, vertexMap, comp_zero, sub_self, zero_comp]

/-- The assembled degree-zero map on the section-representer Cech chain. -/
def onC₀ (U : X.Opens) (x : X) :
    (sectionRepresenterCechChain X.ringCatSheaf (opens U x)).X 0 ⟶
      sectionRepresenter X.ringCatSheaf U :=
  sectionRepresenterCechVertexMap X.ringCatSheaf (opens U x)
    (sectionRepresenter X.ringCatSheaf U) (vertexMap U x)

set_option backward.isDefEq.respectTransparency false in
/-- Assemble the actual first Koszul lifts into a degree-one comparison
map satisfying the Cech differential square. -/
theorem exists_onC₁
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (q f : Γ(X, U))
    (haway : ∀ (z : X) (hz : z ∈ U), z ≠ x →
      Ideal.span ({X.presheaf.germ U z hz q,
        X.presheaf.germ U z hz f} : Set (X.presheaf.stalk z)) = ⊤) :
    ∃ a₁ : (sectionRepresenterCechChain X.ringCatSheaf (opens U x)).X 1 ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U,
      a₁ ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
        (sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d 1 0 ≫ onC₀ U x := by
  classical
  have hlocal (s : Fin 2 → Index X x) :
      ∃ v : sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 2 => opens U x (s k)) ⟶
          ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U,
        v ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
          (sectionRepresenterFunctor X.ringCatSheaf).map
              (Pi.π (fun k : Fin 2 => opens U x (s k)) 1) ≫ vertexMap U x (s 1) -
            (sectionRepresenterFunctor X.ringCatSheaf).map
              (Pi.π (fun k : Fin 2 => opens U x (s k)) 0) ≫ vertexMap U x (s 0) := by
    let e : (∏ᶜ fun k : Fin 2 => opens U x (s k)) ⟶ pairOpen U x (s 0) (s 1) :=
      Pi.lift (fun k : Fin 2 => homOfLE (by
        fin_cases k
        · exact (Pi.π (fun k : Fin 2 => opens U x (s k)) 0).le
        · exact (Pi.π (fun k : Fin 2 => opens U x (s k)) 1).le))
    have he₀ : e ≫ Pi.π ![opens U x (s 0), opens U x (s 1)] 0 =
        Pi.π (fun k : Fin 2 => opens U x (s k)) 0 := Subsingleton.elim _ _
    have he₁ : e ≫ Pi.π ![opens U x (s 0), opens U x (s 1)] 1 =
        Pi.π (fun k : Fin 2 => opens U x (s k)) 1 := Subsingleton.elim _ _
    obtain ⟨v, hv⟩ := exists_pairBoundary_lift U hU x q f haway (s 0) (s 1)
    refine ⟨(sectionRepresenterFunctor X.ringCatSheaf).map e ≫ v, ?_⟩
    rw [Category.assoc, hv]
    change (sectionRepresenterFunctor X.ringCatSheaf).map e ≫
      ((sectionRepresenterFunctor X.ringCatSheaf).map
          (Pi.π ![opens U x (s 0), opens U x (s 1)] 1) ≫ vertexMap U x (s 1) -
        (sectionRepresenterFunctor X.ringCatSheaf).map
          (Pi.π ![opens U x (s 0), opens U x (s 1)] 0) ≫ vertexMap U x (s 0)) = _
    rw [Preadditive.comp_sub, ← Category.assoc, ← Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp, he₁, he₀]
  let a : ∀ s : Fin 2 → Index X x,
      sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 2 => opens U x (s k)) ⟶
        ⨁ sectionRepresenterKoszulPair X.ringCatSheaf U :=
    fun s => Classical.choose (hlocal s)
  refine ⟨Sigma.desc a, ?_⟩
  apply Sigma.hom_ext
  intro s
  rw [← Category.assoc, Sigma.ι_desc]
  change a s ≫ sectionRepresenterKoszulLast X.ringCatSheaf U q f =
    Sigma.ι (fun g : Fin 2 → Index X x =>
      sectionRepresenter X.ringCatSheaf (∏ᶜ fun k : Fin 2 => opens U x (g k))) s ≫
      (sectionRepresenterCechChain X.ringCatSheaf (opens U x)).d 1 0 ≫
        sectionRepresenterCechVertexMap X.ringCatSheaf (opens U x)
          (sectionRepresenter X.ringCatSheaf U) (vertexMap U x)
  rw [sectionRepresenterCechVertexMap_boundary_component]
  exact Classical.choose_spec (hlocal s)

end PfaffianDescent.PointAdaptedAffineCover
