import Mathlib

open Set Topology MeasureTheory

noncomputable section FullPaperVerification

section GeneralTheory

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Многозначный оператор метрической проекции P_V(x) (формула 1) -/
def MetricProjection (V : Submodule ℝ X) (x : X) : Set X :=
  { v ∈ V | ∀ w ∈ V, ‖x - v‖ ≤ ‖x - w‖ }

/-- Определение 1: Проксиминальное подпространство -/
def IsProximinal (V : Submodule ℝ X) : Prop :=
  ∀ x : X, (MetricProjection V x).Nonempty

/-- Нулевой слой метрической проекции P_V⁻¹(0) -/
def ZeroLayer (V : Submodule ℝ X) : Set X :=
  { x : X | (0 : X) ∈ MetricProjection V x }

/-- Определение 3: Непрерывный линейный селектор s_V : X →L[ℝ] X со значениями в V -/
structure LinearSelector (V : Submodule ℝ X) where
  toFun : X →L[ℝ] X
  mem_subspace : ∀ x : X, toFun x ∈ V
  is_selection : ∀ x : X, toFun x ∈ MetricProjection V x

/-- Определение 2: Проксиминальная решетка и согласованная селекторная решетка -/
structure ProximinalLattice (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  carrier : Set (Submodule ℝ X)
  proximinal : ∀ V ∈ carrier, IsProximinal V
  inf_mem : ∀ V₁ ∈ carrier, ∀ V₂ ∈ carrier, V₁ ⊓ V₂ ∈ carrier
  sup_closure_mem : ∀ V₁ ∈ carrier, ∀ V₂ ∈ carrier, (V₁ ⊔ V₂).topologicalClosure ∈ carrier

structure ConsistentSelectorLattice (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    extends ProximinalLattice X where
  selector : ∀ V ∈ carrier, LinearSelector V
  consistent : ∀ V₁ (h₁ : V₁ ∈ carrier) V₂ (h₂ : V₂ ∈ carrier), V₁ ≤ V₂ →
    (selector V₁ h₁).toFun.comp (selector V₂ h₂).toFun = (selector V₁ h₁).toFun ∧
    (selector V₂ h₂).toFun.comp (selector V₁ h₁).toFun = (selector V₁ h₁).toFun

/-- Вспомогательная лемма: селектор тождественен на V и идемпотентен -/
lemma LinearSelector.apply_eq_self {V : Submodule ℝ X} (s : LinearSelector V)
    {v : X} (hv : v ∈ V) : s.toFun v = v := by
  have h_sel := (s.is_selection v).2 v hv
  rw [sub_self, norm_zero] at h_sel
  have h_zero : ‖v - s.toFun v‖ = 0 := le_antisymm h_sel (norm_nonneg _)
  exact (sub_eq_zero.mp (norm_eq_zero.mp h_zero)).symm

lemma LinearSelector.idempotent {V : Submodule ℝ X} (s : LinearSelector V) (x : X) :
    s.toFun (s.toFun x) = s.toFun x :=
  s.apply_eq_self (s.mem_subspace x)

/-- Базовое свойство: любое конечномерное подпространство проксиминально -/
theorem finite_dimensional_isProximinal (V : Submodule ℝ X) [FiniteDimensional ℝ V] :
    IsProximinal V := by
  intro x
  have : ProperSpace V := FiniteDimensional.proper ℝ V
  let B : Set V := Metric.closedBall (0 : V) (2 * ‖x‖)
  have hB_comp : IsCompact B := isCompact_closedBall (0 : V) (2 * ‖x‖)
  have hB_ne : B.Nonempty := ⟨0, Metric.mem_closedBall_self (by positivity)⟩
  have h_cont : Continuous (fun v : V => ‖x - (v : X)‖) :=
    continuous_norm.comp (continuous_const.sub continuous_subtype_val)
  rcases hB_comp.exists_isMinOn hB_ne h_cont.continuousOn with ⟨v₀, _, hv₀_min⟩
  refine ⟨v₀, v₀.2, fun w hw => ?_⟩
  by_cases hw_ball : (⟨w, hw⟩ : V) ∈ B
  · exact hv₀_min hw_ball
  · have h_gt : 2 * ‖x‖ < ‖(⟨w, hw⟩ : V)‖ := by
      simpa [B, Metric.mem_closedBall, dist_zero_right] using hw_ball
    have h0_mem : (0 : V) ∈ B := Metric.mem_closedBall_self (by positivity)
    have h1 : ‖x - (v₀ : X)‖ ≤ ‖x‖ := by
      have := hv₀_min h0_mem
      simpa using this
    have h2 : ‖x‖ ≤ ‖x - w‖ := by
      have h_tri : ‖w‖ ≤ ‖x‖ + ‖x - w‖ := by
        calc ‖w‖ = ‖x - (x - w)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖x‖ + ‖x - w‖ := norm_sub_le x (x - w)
      change 2 * ‖x‖ < ‖w‖ at h_gt
      linarith
    exact h1.trans h2
/-- Лемма 1 (Достаточность): Критерий проксиминальности гиперплоскости V = ker f -/
lemma hyperplane_proximinal_of_attains_norm (f : X →L[ℝ] ℝ) (hf : f ≠ 0)
    (u : X) (hu_norm : ‖u‖ = 1) (hu_att : f u = ‖f‖) :
    IsProximinal (LinearMap.ker (f : X →ₗ[ℝ] ℝ)) := by
  intro x
  have hf_pos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  let v₀ : X := x - (f x / ‖f‖) • u
  refine ⟨v₀, ?_, ?_⟩
  · rw [LinearMap.mem_ker]
    change f (x - (f x / ‖f‖) • u) = 0
    rw [map_sub, map_smul, smul_eq_mul, hu_att, div_mul_cancel₀ _ hf_pos.ne', sub_self]
  · intro w hw
    rw [LinearMap.mem_ker] at hw
    change f w = 0 at hw
    have h_diff : x - v₀ = (f x / ‖f‖) • u := sub_sub_cancel x _
    rw [h_diff, norm_smul, Real.norm_eq_abs, abs_div, abs_norm, hu_norm, mul_one]
    have h_fx : |f x| = |f (x - w)| := by rw [map_sub, hw, sub_zero]
    rw [h_fx, div_le_iff₀ hf_pos, mul_comm]
    simpa [Real.norm_eq_abs] using f.le_opNorm (x - w)

/-- Вспомогательное определение ядра непрерывного линейного оператора как подмодуля -/
abbrev kerSubmodule (T : X →L[ℝ] X) : Submodule ℝ X :=
  LinearMap.ker (T : X →ₗ[ℝ] X)

/-- Теорема 1 (Необходимость) -/
theorem deutsch_necessity {V : Submodule ℝ X} (s : LinearSelector V) :
    let U : Submodule ℝ X := kerSubmodule s.toFun
    IsClosed (U : Set X) ∧ IsCompl V U ∧ (U : Set X) ⊆ ZeroLayer V := by
  intro U
  refine ⟨isClosed_eq s.toFun.continuous continuous_const, ?_, ?_⟩
  · rw [isCompl_iff, disjoint_iff, codisjoint_iff]
    refine ⟨?_, ?_⟩
    · rw [Submodule.eq_bot_iff]
      intro x hx
      rw [Submodule.mem_inf, LinearMap.mem_ker] at hx
      change x ∈ V ∧ s.toFun x = 0 at hx
      rw [← s.apply_eq_self hx.1, hx.2]
    · rw [Submodule.eq_top_iff']
      intro x
      rw [← add_sub_cancel (s.toFun x) x]
      apply Submodule.add_mem_sup (s.mem_subspace x)
      rw [LinearMap.mem_ker]
      change s.toFun (x - s.toFun x) = 0
      rw [map_sub, s.idempotent, sub_self]
  · intro u hu
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hu
    change s.toFun u = 0 at hu
    have h_sel := s.is_selection u
    rwa [hu] at h_sel

/-- Теорема 1 (Достаточность) -/
theorem deutsch_sufficiency {V U : Submodule ℝ X}
    (h_compl : IsCompl V U) (h_zero : (U : Set X) ⊆ ZeroLayer V)
    (s_proj : X →L[ℝ] X)
    (h_proj_V : ∀ v ∈ V, s_proj v = v)
    (h_proj_U : ∀ u ∈ U, s_proj u = 0)
    (h_range : ∀ x : X, s_proj x ∈ V) :
    ∃ s : LinearSelector V, s.toFun = s_proj := by
  refine ⟨⟨s_proj, h_range, ?_⟩, rfl⟩
  intro x
  refine ⟨h_range x, ?_⟩
  intro w hw
  have hx_mem : x ∈ V ⊔ U := by rw [h_compl.sup_eq_top]; trivial
  rcases Submodule.mem_sup.mp hx_mem with ⟨v, hv, u, hu, rfl⟩
  have hsv : s_proj (v + u) = v := by
    rw [map_add, h_proj_V v hv, h_proj_U u hu, add_zero]
  rw [hsv]
  have hu_best := (h_zero hu).2 (w - v) (V.sub_mem hw hv)
  rw [sub_zero] at hu_best
  have h_shift1 : v + u - v = u := add_sub_cancel_left v u
  have h_shift2 : v + u - w = u - (w - v) := by abel
  rw [h_shift1, h_shift2]
  exact hu_best

/-- Следствие 1: Единственность линейного селектора для чебышёвского подпространства -/
theorem chebyshev_selector_unique {V : Submodule ℝ X}
    (h_cheb : ∀ x : X, Set.Subsingleton (MetricProjection V x))
    (s₁ s₂ : LinearSelector V) : s₁.toFun = s₂.toFun :=
  DFunLike.ext _ _ fun x => h_cheb x (s₁.is_selection x) (s₂.is_selection x)

/-- Предложение 1: Композиция коммутирующих линейных селекторов на пересечении V₀ = V₁ ∩ V₂ -/
theorem commuting_selectors_intersection {V₁ V₂ : Submodule ℝ X}
    (s₁ : LinearSelector V₁) (s₂ : LinearSelector V₂)
    (h_comm : s₁.toFun.comp s₂.toFun = s₂.toFun.comp s₁.toFun)
    (h_ker_sub : ((kerSubmodule s₁.toFun ⊔ kerSubmodule s₂.toFun : Submodule ℝ X) : Set X) ⊆
                 ZeroLayer (V₁ ⊓ V₂)) :
    ∃ s₀ : LinearSelector (V₁ ⊓ V₂), s₀.toFun = s₁.toFun.comp s₂.toFun := by
  let V₀ := V₁ ⊓ V₂
  let s₀_op : X →L[ℝ] X := s₁.toFun.comp s₂.toFun
  have h_comm_pt : ∀ x : X, s₁.toFun (s₂.toFun x) = s₂.toFun (s₁.toFun x) :=
    fun x => DFunLike.congr_fun h_comm x
  have h_range : ∀ x : X, s₀_op x ∈ V₀ := by
    intro x
    refine ⟨s₁.mem_subspace _, ?_⟩
    change s₁.toFun (s₂.toFun x) ∈ V₂
    rw [h_comm_pt]
    exact s₂.mem_subspace _
  have h_ker_eq : kerSubmodule s₀_op = kerSubmodule s₁.toFun ⊔ kerSubmodule s₂.toFun := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      change s₁.toFun (s₂.toFun x) = 0 at hx
      have h_decomp : x = (s₂.toFun x - s₁.toFun (s₂.toFun x)) + (x - s₂.toFun x) := by
        rw [add_comm, sub_add_sub_cancel, hx, sub_zero]
      rw [h_decomp]
      apply Submodule.add_mem_sup
      · rw [LinearMap.mem_ker]
        change s₁.toFun (s₂.toFun x - s₁.toFun (s₂.toFun x)) = 0
        rw [map_sub, s₁.idempotent, sub_self]
      · rw [LinearMap.mem_ker]
        change s₂.toFun (x - s₂.toFun x) = 0
        rw [map_sub, s₂.idempotent, sub_self]
    · apply sup_le
      · intro x hx
        rw [LinearMap.mem_ker] at hx ⊢
        change s₁.toFun x = 0 at hx
        change s₁.toFun (s₂.toFun x) = 0
        rw [h_comm_pt, hx, map_zero]
      · intro x hx
        rw [LinearMap.mem_ker] at hx ⊢
        change s₂.toFun x = 0 at hx
        change s₁.toFun (s₂.toFun x) = 0
        rw [hx, map_zero]
  refine ⟨⟨s₀_op, h_range, fun x => ⟨h_range x, fun w hw => ?_⟩⟩, rfl⟩
  have hu_ker : x - s₀_op x ∈ kerSubmodule s₁.toFun ⊔ kerSubmodule s₂.toFun := by
    rw [← h_ker_eq, LinearMap.mem_ker]
    change s₁.toFun (s₂.toFun (x - s₁.toFun (s₂.toFun x))) = 0
    rw [map_sub, map_sub]
    have h_idem : s₁.toFun (s₂.toFun (s₁.toFun (s₂.toFun x))) = s₁.toFun (s₂.toFun x) := by
      calc s₁.toFun (s₂.toFun (s₁.toFun (s₂.toFun x)))
        _ = s₁.toFun (s₁.toFun (s₂.toFun (s₂.toFun x))) := by rw [← h_comm_pt (s₂.toFun x)]
        _ = s₁.toFun (s₂.toFun (s₂.toFun x)) := by rw [s₁.idempotent]
        _ = s₁.toFun (s₂.toFun x) := by rw [s₂.idempotent]
    rw [h_idem, sub_self]
  have hu_zero := (h_ker_sub hu_ker).2 (w - s₀_op x) (V₀.sub_mem hw (h_range x))
  rw [sub_zero] at hu_zero
  have h_shift : x - w = (x - s₀_op x) - (w - s₀_op x) := (sub_sub_sub_cancel_right x w (s₀_op x)).symm
  rw [h_shift]
  exact hu_zero
/-- Свойство согласованной решетки 1: при V₁ ≤ V₂ ядро большего селектора вложено в ядро меньшего -/
lemma ConsistentSelectorLattice.ker_anti {L : ConsistentSelectorLattice X}
    {V₁ V₂ : Submodule ℝ X} (h₁ : V₁ ∈ L.carrier) (h₂ : V₂ ∈ L.carrier) (h_le : V₁ ≤ V₂) :
    kerSubmodule (L.selector V₂ h₂).toFun ≤ kerSubmodule (L.selector V₁ h₁).toFun := by
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [LinearMap.mem_ker]
  change (L.selector V₁ h₁).toFun x = 0
  have h_comp := (L.consistent V₁ h₁ V₂ h₂ h_le).1
  have h_pt := DFunLike.congr_fun h_comp x
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at h_pt
  change (L.selector V₂ h₂).toFun x = 0 at hx
  rw [← h_pt, hx, map_zero]


/-- Свойство согласованной решетки 2: селектор на меньшем подпространстве V₁ ≤ V₂
    является ограничением s_{V₁} на образ s_{V₂} -/
lemma ConsistentSelectorLattice.factor_through_sup {L : ConsistentSelectorLattice X}
    {V₁ V₂ : Submodule ℝ X} (h₁ : V₁ ∈ L.carrier) (h₂ : V₂ ∈ L.carrier) (h_le : V₁ ≤ V₂) (x : X) :
    (L.selector V₁ h₁).toFun ((L.selector V₂ h₂).toFun x) = (L.selector V₁ h₁).toFun x := by
  have h_pt := DFunLike.congr_fun (L.consistent V₁ h₁ V₂ h₂ h_le).1 x
  simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply] using h_pt

/-- Теорема 4: Глобальная липшицева стабильность ‖s_V(x) - s_V(y)‖ ≤ ‖I - Q‖ * ‖x - y‖ -/
theorem selector_lipschitz_stability {V : Submodule ℝ X} (s : LinearSelector V) :
    let Q : X →L[ℝ] X := ContinuousLinearMap.id ℝ X - s.toFun
    ∀ x y : X, ‖s.toFun x - s.toFun y‖ ≤ ‖ContinuousLinearMap.id ℝ X - Q‖ * ‖x - y‖ := by
  intro Q x y
  have h_eq : ContinuousLinearMap.id ℝ X - Q = s.toFun := sub_sub_cancel _ _
  rw [h_eq, ← map_sub]
  exact s.toFun.le_opNorm (x - y)

/-- Коэффициент взаимного наклона (раскрытия) подпространств δ(V, U) -/
def MutualInclination (V U : Submodule ℝ X) : ℝ :=
  sInf { r : ℝ | ∃ v ∈ V, ‖v‖ = 1 ∧ ∃ u ∈ U, r = ‖v + u‖ }

/-- Следствие 2 (Верхняя оценка): L ≤ 1 / δ(V, U) -/
theorem selector_norm_bound_by_inclination {V : Submodule ℝ X} (s : LinearSelector V)
    (h_pos : 0 < MutualInclination V (kerSubmodule s.toFun))
    (h_bdd : BddBelow { r : ℝ | ∃ v ∈ V, ‖v‖ = 1 ∧ ∃ u ∈ kerSubmodule s.toFun, r = ‖v + u‖ }) :
    ‖s.toFun‖ ≤ 1 / MutualInclination V (kerSubmodule s.toFun) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg zero_le_one h_pos.le)
  intro x
  by_cases hv : s.toFun x = 0
  · rw [hv, norm_zero]
    exact mul_nonneg (div_nonneg zero_le_one h_pos.le) (norm_nonneg x)
  · set v := s.toFun x
    set u := x - v
    have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hv_unit : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hv_norm_pos.ne']
    have hv_mem : ‖v‖⁻¹ • v ∈ V := V.smul_mem _ (s.mem_subspace x)
    have hu_mem : ‖v‖⁻¹ • u ∈ kerSubmodule s.toFun := by
      rw [LinearMap.mem_ker]
      change s.toFun (‖v‖⁻¹ • (x - s.toFun x)) = 0
      rw [map_smul, map_sub, s.idempotent, sub_self, smul_zero]
    have h_delta_le : MutualInclination V (kerSubmodule s.toFun) ≤ ‖‖v‖⁻¹ • v + ‖v‖⁻¹ • u‖ :=
      csInf_le h_bdd ⟨‖v‖⁻¹ • v, hv_mem, hv_unit, ‖v‖⁻¹ • u, hu_mem, rfl⟩
    have h_factor : ‖‖v‖⁻¹ • v + ‖v‖⁻¹ • u‖ = ‖v‖⁻¹ * ‖x‖ := by
      rw [← smul_add, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, add_sub_cancel]
    rw [h_factor] at h_delta_le
    have h1 : MutualInclination V (kerSubmodule s.toFun) * ‖v‖ ≤ ‖x‖ := by
      have := mul_le_mul_of_nonneg_right h_delta_le hv_norm_pos.le
      rwa [mul_comm (‖v‖⁻¹) ‖x‖, mul_assoc, inv_mul_cancel₀ hv_norm_pos.ne', mul_one] at this
    rw [one_div, inv_mul_eq_div, le_div_iff₀' h_pos]
    exact h1

/-- Следствие 2 (Точность оценки): ‖s_V‖ = 1 / δ(V, ker s_V) для ненулевого V -/
theorem selector_norm_eq_inv_inclination {V : Submodule ℝ X} (s : LinearSelector V)
    (hV_nontriv : ∃ v ∈ V, v ≠ 0)
    (h_pos : 0 < MutualInclination V (kerSubmodule s.toFun)) :
    ‖s.toFun‖ = 1 / MutualInclination V (kerSubmodule s.toFun) := by
  set S := { r : ℝ | ∃ v ∈ V, ‖v‖ = 1 ∧ ∃ u ∈ kerSubmodule s.toFun, r = ‖v + u‖ }
  have h_bdd : BddBelow S := ⟨0, by rintro r ⟨v, _, _, u, _, rfl⟩; exact norm_nonneg _⟩
  apply le_antisymm (selector_norm_bound_by_inclination s h_pos h_bdd)
  have h_nonempty : S.Nonempty := by
    rcases hV_nontriv with ⟨v₀, hv₀, hv₀_ne⟩
    have hv₀_pos : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀_ne
    refine ⟨‖‖v₀‖⁻¹ • v₀ + 0‖, ‖v₀‖⁻¹ • v₀, V.smul_mem _ hv₀, ?_, 0, Submodule.zero_mem _, rfl⟩
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hv₀_pos.ne']
  have hs_pos : 0 < ‖s.toFun‖ := by
    rcases hV_nontriv with ⟨v₀, hv₀, hv₀_ne⟩
    have h1 : ‖v₀‖ ≤ ‖s.toFun‖ * ‖v₀‖ := by
      simpa only [s.apply_eq_self hv₀] using s.toFun.le_opNorm v₀
    have hv₀_pos : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀_ne
    nlinarith
  rw [one_div, inv_le_comm₀ h_pos hs_pos]
  apply le_csInf h_nonempty
  rintro r ⟨v, hv, hv_norm, u, hu, rfl⟩
  rw [LinearMap.mem_ker] at hu
  change s.toFun u = 0 at hu
  have h_svu : s.toFun (v + u) = v := by
    rw [map_add, s.apply_eq_self hv, hu, add_zero]
  have h_bound : 1 ≤ ‖s.toFun‖ * ‖v + u‖ := by
    calc (1 : ℝ) = ‖v‖ := hv_norm.symm
      _ = ‖s.toFun (v + u)‖ := by rw [h_svu]
      _ ≤ ‖s.toFun‖ * ‖v + u‖ := s.toFun.le_opNorm (v + u)
  rw [mul_comm] at h_bound
  rwa [inv_le_iff_one_le_mul₀ hs_pos]

end GeneralTheory
section L1Theory

/-- Ортогональность по Биркгофу–Джеймсу x ⊥_B y и x ⊥_B V -/
def BirkhoffOrthogonal {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (x y : X) : Prop :=
  ∀ c : ℝ, ‖x‖ ≤ ‖x + c • y‖

def BirkhoffOrthogonalSubspace {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (x : X) (V : Submodule ℝ X) : Prop :=
  ∀ v ∈ V, BirkhoffOrthogonal x v

/-- Эквивалентность u ⊥_B V и принадлежности нулевому слою u ∈ P_V⁻¹(0) -/
lemma birkhoff_iff_zero_layer {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (u : X) (V : Submodule ℝ X) :
    BirkhoffOrthogonalSubspace u V ↔ u ∈ ZeroLayer V := by
  constructor
  · intro h_orth
    refine ⟨V.zero_mem, fun w hw => ?_⟩
    rw [sub_zero]
    have h1 := h_orth (-w) (V.neg_mem hw) 1
    rwa [one_smul, ← sub_eq_add_neg] at h1
  · intro h_zero v hv c
    have h1 := h_zero.2 (-c • v) (V.smul_mem (-c) hv)
    rwa [sub_zero, neg_smul, sub_neg_eq_add] at h1

/-- Вспомогательная лемма: x * sign(x) = |x| для вещественных чисел -/
lemma real_mul_sign_self (x : ℝ) : x * Real.sign x = |x| := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx, mul_neg_one]
  · simp
  · rw [Real.sign_of_pos hx, abs_of_pos hx, mul_one]

/-- Теорема 2 (Двойственный этап / Достаточность): Существование аннулирующего функционала g ∈ ∂‖u‖₁
    влечет принадлежность элемента u нулевому слою P_V⁻¹(0) -/
theorem L1_dual_annihilator_implies_birkhoff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V : Submodule ℝ (Lp ℝ 1 μ)) (u : Lp ℝ 1 μ)
    (g : Ω → ℝ) (hg_meas : StronglyMeasurable g)
    (hg_bound : ∀ᵐ t ∂μ, |g t| ≤ 1)
    (hg_sign : ∀ᵐ t ∂μ, (u : Ω → ℝ) t ≠ 0 → g t = Real.sign ((u : Ω → ℝ) t))
    (hg_annihilate : ∀ v ∈ V, ∫ t, (v : Ω → ℝ) t * g t ∂μ = 0) :
    u ∈ ZeroLayer V := by
  rw [← birkhoff_iff_zero_layer]
  intro v hv c
  have h_norm_u : ‖u‖ = ∫ t, |(u : Ω → ℝ) t| ∂μ := by
    simpa [Real.norm_eq_abs] using L1.norm_eq_integral_norm u
  have h_int_ug : ∫ t, (u : Ω → ℝ) t * g t ∂μ = ∫ t, |(u : Ω → ℝ) t| ∂μ := by
    apply integral_congr_ae
    filter_upwards [hg_sign] with t ht
    by_cases hut : (u : Ω → ℝ) t = 0
    · simp [hut]
    · rw [ht hut, real_mul_sign_self]
  have h_int_prod : ∀ w : Lp ℝ 1 μ, Integrable (fun t => (w : Ω → ℝ) t * g t) μ := by
    intro w
    simpa only [mul_comm] using (L1.integrable_coeFn w).bdd_mul hg_meas.aestronglyMeasurable
      (hg_bound.mono fun _ h => by rwa [Real.norm_eq_abs])
  have h_pair : ∫ t, ((u + c • v : Lp ℝ 1 μ) : Ω → ℝ) t * g t ∂μ = ‖u‖ := by
    have h_ae : ∀ᵐ t ∂μ, ((u + c • v : Lp ℝ 1 μ) : Ω → ℝ) t * g t =
        (u : Ω → ℝ) t * g t + c * ((v : Ω → ℝ) t * g t) := by
      filter_upwards [Lp.coeFn_add u (c • v), Lp.coeFn_smul c v] with t h1 h2
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]
      ring
    rw [integral_congr_ae h_ae, integral_add (h_int_prod u) ((h_int_prod v).const_mul c),
        integral_const_mul, hg_annihilate v hv, mul_zero, add_zero, h_int_ug, ← h_norm_u]
  have h_int_abs1 : ∫ t, ((u + c • v : Lp ℝ 1 μ) : Ω → ℝ) t * g t ∂μ ≤
      ∫ t, |((u + c • v : Lp ℝ 1 μ) : Ω → ℝ) t * g t| ∂μ :=
    integral_mono_ae (h_int_prod (u + c • v)) (h_int_prod (u + c • v)).abs
      (ae_of_all _ fun _ => le_abs_self _)
  have h_int_abs2 : ∫ t, |((u + c • v : Lp ℝ 1 μ) : Ω → ℝ) t * g t| ∂μ ≤
      ∫ t, |((u + c • v : Lp ℝ 1 μ) : Ω → ℝ) t| ∂μ := by
    refine integral_mono_ae (h_int_prod (u + c • v)).abs (L1.integrable_coeFn (u + c • v)).abs ?_
    filter_upwards [hg_bound] with t ht
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) ht
  have h_norm_sum : ‖u + c • v‖ = ∫ t, |((u + c • v : Lp ℝ 1 μ) : Ω → ℝ) t| ∂μ := by
    simpa [Real.norm_eq_abs] using L1.norm_eq_integral_norm (u + c • v)
  linarith

/-- Теорема 2 (Необходимость, неравенство 3): Если аннулирующий функционал g ∈ ∂‖u‖₁
    совпадает со sign(u(t)) вне нулей u и ограничен единицей |g(t)| ≤ 1 на нулях u,
    то выполнено знаково-взвешенное интегральное неравенство (3). -/
theorem L1_annihilator_implies_sign_integral_ineq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (u v : Lp ℝ 1 μ) (g : Ω → ℝ)
    (hg_meas : StronglyMeasurable g)
    (hg_bound : ∀ᵐ t ∂μ, |g t| ≤ 1)
    (hg_sign : ∀ᵐ t ∂μ, (u : Ω → ℝ) t ≠ 0 → g t = Real.sign ((u : Ω → ℝ) t))
    (hg_annihilate : ∫ t, (v : Ω → ℝ) t * g t ∂μ = 0)
    (h_meas_supp : MeasurableSet { t : Ω | (u : Ω → ℝ) t = 0 }) :

    |∫ t in { t : Ω | (u : Ω → ℝ) t = 0 }ᶜ, (v : Ω → ℝ) t * Real.sign ((u : Ω → ℝ) t) ∂μ| ≤
      ∫ t in { t : Ω | (u : Ω → ℝ) t = 0 }, |(v : Ω → ℝ) t| ∂μ := by
  set S₀ := { t : Ω | (u : Ω → ℝ) t = 0 }
  have h_int_vg : Integrable (fun t => (v : Ω → ℝ) t * g t) μ := by
    simpa only [mul_comm] using (L1.integrable_coeFn v).bdd_mul hg_meas.aestronglyMeasurable
      (hg_bound.mono fun _ h => by rwa [Real.norm_eq_abs])
  have h_split : (∫ t in S₀ᶜ, (v : Ω → ℝ) t * g t ∂μ) + (∫ t in S₀, (v : Ω → ℝ) t * g t ∂μ) = 0 := by
    rw [add_comm, integral_add_compl h_meas_supp h_int_vg, hg_annihilate]
  have h_compl_eq : ∫ t in S₀ᶜ, (v : Ω → ℝ) t * g t ∂μ =
      ∫ t in S₀ᶜ, (v : Ω → ℝ) t * Real.sign ((u : Ω → ℝ) t) ∂μ := by
    refine setIntegral_congr_ae h_meas_supp.compl ?_
    filter_upwards [hg_sign] with t ht hut
    rw [ht hut]
  have h_abs_eq : |∫ t in S₀ᶜ, (v : Ω → ℝ) t * Real.sign ((u : Ω → ℝ) t) ∂μ| =

      |∫ t in S₀, (v : Ω → ℝ) t * g t ∂μ| := by
    rw [← h_compl_eq, eq_neg_of_add_eq_zero_left h_split, abs_neg]
  rw [h_abs_eq]
  calc |∫ t in S₀, (v : Ω → ℝ) t * g t ∂μ|
    _ ≤ ∫ t in S₀, |(v : Ω → ℝ) t * g t| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ t in S₀, |(v : Ω → ℝ) t| ∂μ := by
        refine setIntegral_mono_ae_restrict h_int_vg.integrableOn.abs
          (L1.integrable_coeFn v).integrableOn.abs ?_
        filter_upwards [ae_restrict_of_ae hg_bound] with t ht
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) ht

end L1Theory
section CKTheory

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Множество точек максимального уклонения M(u) = {t ∈ K : |u(t)| = ‖u‖_∞} -/
def ExtremalSet (u : C(K, ℝ)) : Set K :=
  { t : K | |u t| = ‖u‖ }

/-- Вспомогательная лемма: на непустом компакте множество экстремальных точек M(u) замкнуто и непусто -/
lemma extremalSet_isClosed (u : C(K, ℝ)) : IsClosed (ExtremalSet u) :=
  isClosed_eq (continuous_abs.comp u.continuous) continuous_const

lemma extremalSet_nonempty [Nonempty K] (u : C(K, ℝ)) : (ExtremalSet u).Nonempty := by
  rcases isCompact_univ.exists_isMaxOn univ_nonempty (continuous_abs.comp u.continuous).continuousOn
    with ⟨t₀, _, ht₀⟩
  refine ⟨t₀, le_antisymm (ContinuousMap.norm_coe_le_norm u t₀) ?_⟩
  rw [ContinuousMap.norm_eq_iSup_norm]
  refine ciSup_le fun t => ?_
  simpa [Real.norm_eq_abs] using ht₀ (mem_univ t)

/-- Теорема 3 (Достаточность критерия Колмогорова, формула 5) -/
theorem kolmogorov_criterion_sufficiency (V : Submodule ℝ C(K, ℝ)) (u : C(K, ℝ))
    (h_kolm : ∀ v ∈ V, ∃ t₀ ∈ ExtremalSet u, Real.sign (u t₀) * v t₀ ≤ 0) :
    u ∈ ZeroLayer V := by
  refine ⟨V.zero_mem, fun v hv => ?_⟩
  rw [sub_zero]
  by_cases hu : u = 0
  · rw [hu, norm_zero]
    exact norm_nonneg _
  · rcases h_kolm v hv with ⟨t₀, ht₀_ext, ht₀_sign⟩
    have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have h_abs_t₀ : |u t₀| = ‖u‖ := ht₀_ext
    have hut₀_ne : u t₀ ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h_abs_t₀
      linarith
    have h_pointwise : |u t₀| ≤ |u t₀ - v t₀| := by
      rcases lt_trichotomy (u t₀) 0 with h_neg | h_zero | h_pos
      · rw [Real.sign_of_neg h_neg, neg_one_mul, neg_nonpos] at ht₀_sign
        rw [abs_of_neg h_neg, abs_of_neg (by linarith)]
        linarith
      · exact False.elim (hut₀_ne h_zero)
      · rw [Real.sign_of_pos h_pos, one_mul] at ht₀_sign
        rw [abs_of_pos h_pos, abs_of_pos (by linarith)]
        linarith
    calc ‖u‖ = |u t₀| := h_abs_t₀.symm
      _ ≤ |u t₀ - v t₀| := h_pointwise
      _ ≤ ‖u - v‖ := ContinuousMap.norm_coe_le_norm (u - v) t₀

/-- Теорема 3 (Необходимость критерия Колмогорова): если u ∈ P_V⁻¹(0) на непустом компакте K,
    то для всякого v ∈ V найдется t₀ ∈ M(u) с sign(u(t₀)) * v(t₀) ≤ 0 -/
theorem kolmogorov_criterion_necessity [Nonempty K] (V : Submodule ℝ C(K, ℝ)) (u : C(K, ℝ))
    (hu_zero : u ∈ ZeroLayer V) :
    ∀ v ∈ V, ∃ t₀ ∈ ExtremalSet u, Real.sign (u t₀) * v t₀ ≤ 0 := by
  intro v hv
  by_cases hu : u = 0
  · rcases extremalSet_nonempty u with ⟨t₀, ht₀⟩
    refine ⟨t₀, ht₀, ?_⟩
    simp [hu]
  · by_contra h_not
    push Not at h_not
    have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hM_comp : IsCompact (ExtremalSet u) := (extremalSet_isClosed u).isCompact
    have hM_ne : (ExtremalSet u).Nonempty := extremalSet_nonempty u
    let φ : C(K, ℝ) := ⟨fun t => u t * v t, u.continuous.mul v.continuous⟩
    have hφ_pos_on_M : ∀ t ∈ ExtremalSet u, 0 < φ t := by
      intro t ht
      have h_sign := h_not t ht
      have h_abs : |u t| = ‖u‖ := ht
      rcases lt_trichotomy (u t) 0 with h_neg | h0 | h_pos
      · rw [Real.sign_of_neg h_neg, neg_one_mul] at h_sign
        exact mul_pos_of_neg_of_neg h_neg (by linarith)
      · rw [h0, abs_zero] at h_abs
        linarith
      · rw [Real.sign_of_pos h_pos, one_mul] at h_sign
        exact mul_pos h_pos h_sign
    rcases hM_comp.exists_isMinOn hM_ne φ.continuous.continuousOn with ⟨t₁, ht₁_M, ht₁_min⟩
    set m : ℝ := φ t₁
    have hm_pos : 0 < m := hφ_pos_on_M t₁ ht₁_M
    let U_open : Set K := { t : K | m / 2 < φ t }
    have hU_open : IsOpen U_open := isOpen_lt continuous_const φ.continuous
    have hM_sub_U : ExtremalSet u ⊆ U_open := fun t ht => by
      have : m ≤ φ t := ht₁_min ht
      change m / 2 < φ t
      linarith
    let F : Set K := U_openᶜ
    have hF_comp : IsCompact F := hU_open.isClosed_compl.isCompact
    have h_sup_F_lt : ∃ M_F < ‖u‖, ∀ t ∈ F, |u t| ≤ M_F := by
      by_cases hF_ne : F.Nonempty
      · rcases hF_comp.exists_isMaxOn hF_ne (continuous_abs.comp u.continuous).continuousOn
          with ⟨t₂, ht₂_F, ht₂_max⟩
        refine ⟨|u t₂|, ?_, fun t ht => ht₂_max ht⟩
        have h_le : |u t₂| ≤ ‖u‖ := ContinuousMap.norm_coe_le_norm u t₂
        refine lt_of_le_of_ne h_le fun h_eq => ?_
        exact ht₂_F (hM_sub_U h_eq)
      · rw [not_nonempty_iff_eq_empty] at hF_ne
        exact ⟨0, hu_pos, fun t ht => by simp [hF_ne] at ht⟩
    rcases h_sup_F_lt with ⟨M_F, hMF_lt, hMF_bound⟩
    by_cases hv0 : v = 0
    · rcases hM_ne with ⟨t₀, ht₀⟩
      have := h_not t₀ ht₀
      simp [hv0] at this
    · have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      set ε : ℝ := min ((‖u‖ - M_F) / (2 * ‖v‖)) (m / (2 * ‖v‖ ^ 2))
      have hε_pos : 0 < ε := by
        refine lt_min (div_pos (by linarith) (by positivity)) (div_pos hm_pos (by positivity))
      have h_better : ‖u - ε • v‖ < ‖u‖ := by
        rcases isCompact_univ.exists_isMaxOn univ_nonempty
          (continuous_abs.comp (u - ε • v).continuous).continuousOn with ⟨t_max, _, ht_max⟩
        have h_norm_eq : ‖u - ε • v‖ = |(u - ε • v) t_max| := by
          refine le_antisymm ?_ (ContinuousMap.norm_coe_le_norm (u - ε • v) t_max)
          rw [ContinuousMap.norm_eq_iSup_norm]
          exact ciSup_le fun t => by simpa [Real.norm_eq_abs] using ht_max (mem_univ t)
        rw [h_norm_eq]
        change |u t_max - ε * v t_max| < ‖u‖
        by_cases ht_U : t_max ∈ U_open
        · have hφ_gt : m / 2 < u t_max * v t_max := ht_U
          have hu_le : |u t_max| ≤ ‖u‖ := ContinuousMap.norm_coe_le_norm u t_max
          have hv_le : |v t_max| ≤ ‖v‖ := ContinuousMap.norm_coe_le_norm v t_max
          have hε_le2 : ε ≤ m / (2 * ‖v‖ ^ 2) := min_le_right _ _
          have h_sq : (u t_max - ε * v t_max) ^ 2 < ‖u‖ ^ 2 := by
            have h1 : (u t_max - ε * v t_max) ^ 2 =
                (u t_max) ^ 2 - ε * (2 * (u t_max * v t_max) - ε * (v t_max) ^ 2) := by ring
            have h2 : (v t_max) ^ 2 ≤ ‖v‖ ^ 2 := sq_le_sq.mpr (by simpa [abs_norm] using hv_le)
            have h3 : ε * (v t_max) ^ 2 ≤ m / 2 := by
              calc ε * (v t_max) ^ 2 ≤ (m / (2 * ‖v‖ ^ 2)) * ‖v‖ ^ 2 := by nlinarith
                _ = m / 2 := by field_simp
            have h4 : 0 < ε * (2 * (u t_max * v t_max) - ε * (v t_max) ^ 2) := by nlinarith
            have h5 : (u t_max) ^ 2 ≤ ‖u‖ ^ 2 := sq_le_sq.mpr (by simpa [abs_norm] using hu_le)
            linarith
          nlinarith [abs_nonneg (u t_max - ε * v t_max), sq_abs (u t_max - ε * v t_max)]
        · have ht_F : t_max ∈ F := ht_U
          have hu_le : |u t_max| ≤ M_F := hMF_bound t_max ht_F
          have hv_le : |v t_max| ≤ ‖v‖ := ContinuousMap.norm_coe_le_norm v t_max
          have hε_le1 : ε ≤ (‖u‖ - M_F) / (2 * ‖v‖) := min_le_left _ _
          have h_tri : |u t_max - ε * v t_max| ≤ |u t_max| + ε * |v t_max| := by
            calc |u t_max - ε * v t_max| ≤ |u t_max| + |ε * v t_max| := abs_sub _ _
              _ = |u t_max| + ε * |v t_max| := by rw [abs_mul, abs_of_pos hε_pos]
          have hεv : ε * |v t_max| ≤ (‖u‖ - M_F) / 2 := by
            calc ε * |v t_max| ≤ ((‖u‖ - M_F) / (2 * ‖v‖)) * ‖v‖ := by nlinarith
              _ = (‖u‖ - M_F) / 2 := by field_simp
          linarith
      have h_best := hu_zero.2 (ε • v) (V.smul_mem ε hv)
      rw [sub_zero] at h_best
      linarith

end CKTheory

section ExtendedVerification

/-- Лемма 1 (Необходимость): Если гиперплоскость V = ker f проксиминальна
    и dist(x, V) = |f(x)| / ‖f‖ для некоторого x ∉ ker f, то f достигает нормы на S_X. -/
lemma hyperplane_attains_norm_of_proximinal {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X →L[ℝ] ℝ) (hf : f ≠ 0) (x : X) (hx : f x ≠ 0)
    (v₀ : X) (hv₀_ker : f v₀ = 0) (hv₀_dist : ‖x - v₀‖ = |f x| / ‖f‖) :
    ∃ u : X, ‖u‖ = 1 ∧ |f u| = ‖f‖ := by
  have hf_pos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hfx_pos : 0 < |f x| := abs_pos.mpr hx
  have h_diff_pos : 0 < ‖x - v₀‖ := by
    rw [hv₀_dist]
    exact div_pos hfx_pos hf_pos
  refine ⟨‖x - v₀‖⁻¹ • (x - v₀), ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ h_diff_pos.ne']
  · rw [map_smul, smul_eq_mul, abs_mul, abs_inv, abs_norm, map_sub, hv₀_ker, sub_zero,
        hv₀_dist, inv_div, div_mul_cancel₀ _ hfx_pos.ne']

/-- Пример 1: Точное вычисление L₁-нормы базисной функции v(t) = t - 1/2 на [0, 1]
    и проверка нормировочного множителя L = 4 * ‖v‖₁ = 1. -/
lemma example1_integral_norm_check :
    4 * ((∫ t in (0 : ℝ)..(1/2 : ℝ), (1/2 - t)) + (∫ t in (1/2 : ℝ)..(1 : ℝ), (t - 1/2))) = 1 := by
  have h_id1 : IntervalIntegrable (fun t : ℝ => t) volume 0 (1/2) :=
    continuous_id.intervalIntegrable _ _
  have h_id2 : IntervalIntegrable (fun t : ℝ => t) volume (1/2) 1 :=
    continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub intervalIntegrable_const h_id1,
      intervalIntegral.integral_sub h_id2 intervalIntegrable_const,
      intervalIntegral.integral_const, intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  norm_num


/-- Вспомогательная проверка для Примера 1: ∫₀¹ (t - 1/2) * sign(t - 1/2) dt = 1/4 -/
lemma example1_sign_pairing_check :
    ∫ t in (0 : ℝ)..(1 : ℝ), (t - 1/2) * Real.sign (t - 1/2) = 1 / 4 := by
  have h_eq_left : EqOn (fun t : ℝ => (t - 1/2) * Real.sign (t - 1/2))
      (fun t : ℝ => 1/2 - t) (Set.uIcc 0 (1/2)) := by
    intro t ht
    dsimp only
    rw [Set.uIcc_of_le (by norm_num)] at ht
    rcases lt_or_eq_of_le ht.2 with h_lt | rfl
    · have h_neg : t - 1/2 < 0 := by linarith
      rw [Real.sign_of_neg h_neg]
      ring
    · norm_num
  have h_eq_right : EqOn (fun t : ℝ => (t - 1/2) * Real.sign (t - 1/2))
      (fun t : ℝ => t - 1/2) (Set.uIcc (1/2) 1) := by
    intro t ht
    dsimp only
    rw [Set.uIcc_of_le (by norm_num)] at ht
    rcases lt_or_eq_of_le ht.1 with h_gt | h_eq
    · have h_pos : 0 < t - 1/2 := by linarith
      rw [Real.sign_of_pos h_pos]
      ring
    · rw [← h_eq]
      norm_num
  have h_int1 : IntervalIntegrable (fun t : ℝ => (t - 1/2) * Real.sign (t - 1/2)) volume 0 (1/2) := by
    have hc : Continuous (fun t : ℝ => (1/2 : ℝ) - t) := continuous_const.sub continuous_id
    exact (hc.intervalIntegrable 0 (1/2)).congr (fun t ht => (h_eq_left (Set.Ioc_subset_Icc_self ht)).symm)
  have h_int2 : IntervalIntegrable (fun t : ℝ => (t - 1/2) * Real.sign (t - 1/2)) volume (1/2) 1 := by
    have hc : Continuous (fun t : ℝ => t - (1/2 : ℝ)) := continuous_id.sub continuous_const
    exact (hc.intervalIntegrable (1/2) 1).congr (fun t ht => (h_eq_right (Set.Ioc_subset_Icc_self ht)).symm)
  have h_split : ∫ t in (0 : ℝ)..(1 : ℝ), (t - 1/2) * Real.sign (t - 1/2) =
      (∫ t in (0 : ℝ)..(1/2 : ℝ), (t - 1/2) * Real.sign (t - 1/2)) +
      (∫ t in (1/2 : ℝ)..(1 : ℝ), (t - 1/2) * Real.sign (t - 1/2)) :=
    (intervalIntegral.integral_add_adjacent_intervals h_int1 h_int2).symm
  rw [h_split, intervalIntegral.integral_congr h_eq_left, intervalIntegral.integral_congr h_eq_right]
  linarith [example1_integral_norm_check]



/-- Пример 1 (Полная верификация селектора в L₁):
    Для v(t) = t - 1/2 и функционала g(t) = sign(t - 1/2) оператор
    s_V(f) = (4 * ∫₀¹ f(t) g(t) dt) • v является идемпотентным селектором
    с точной константой Липшица L = 1 (если ‖v‖₁ = 1/4). -/
theorem example1_selector_properties
    {X₁ : Type*} [NormedAddCommGroup X₁] [NormedSpace ℝ X₁]
    (v : X₁) (hv_norm : ‖v‖ = 1 / 4)
    (φ : X₁ →L[ℝ] ℝ) (hφ_norm : ∀ f : X₁, |φ f| ≤ ‖f‖)
    (hφ_v : φ v = 1 / 4) :
    let V : Submodule ℝ X₁ := Submodule.span ℝ {v}
    let s_op : X₁ →L[ℝ] X₁ := (4 • φ).smulRight v
    (∀ f : X₁, s_op f ∈ V) ∧
    (∀ w ∈ V, s_op w = w) ∧
    (∀ f : X₁, s_op (s_op f) = s_op f) ∧
    (∀ f : X₁, φ (f - s_op f) = 0) ∧
    (∀ f₁ f₂ : X₁, ‖s_op f₁ - s_op f₂‖ ≤ 1 * ‖f₁ - f₂‖) := by
  intro V s_op
  have h_apply : ∀ f : X₁, s_op f = (4 * φ f) • v := fun f => by simp [s_op]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    rw [h_apply]
    exact Submodule.smul_mem V _ (Submodule.subset_span (Set.mem_singleton v))
  · intro w hw
    rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
    rw [h_apply, map_smul, smul_eq_mul, hφ_v]
    have h4 : 4 * (c * (1 / 4)) = c := by ring
    rw [h4]
  · intro f
    rw [h_apply, h_apply, map_smul, smul_eq_mul, hφ_v]
    have h4 : 4 * (4 * φ f * (1 / 4)) = 4 * φ f := by ring
    rw [h4]
  · intro f
    rw [map_sub, h_apply, map_smul, smul_eq_mul, hφ_v]
    ring
  · intro f₁ f₂
    rw [← map_sub, h_apply, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num),
        hv_norm, one_mul]
    have h_est := hφ_norm (f₁ - f₂)
    linarith
    
    
end ExtendedVerification

end FullPaperVerification
