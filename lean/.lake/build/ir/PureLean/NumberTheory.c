// Lean compiler output
// Module: PureLean.NumberTheory
// Imports: public import Init public meta import Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section02_powNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section02_powNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumUpTo(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumUpTo___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumOdds(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumOdds___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_pow2N(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_pow2N___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumPow2(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumPow2___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_fibN(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_fibN___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumFib(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumFib___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section02_powNat(lean_object* v_b_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_zero_3_; uint8_t v_isZero_4_; 
v_zero_3_ = lean_unsigned_to_nat(0u);
v_isZero_4_ = lean_nat_dec_eq(v_x_2_, v_zero_3_);
if (v_isZero_4_ == 1)
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(1u);
return v___x_5_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_x_2_, v_one_6_);
v___x_8_ = lp_purelean_PureLean_NumberTheory_Section02_powNat(v_b_1_, v_n_7_);
lean_dec(v_n_7_);
v___x_9_ = lean_nat_mul(v___x_8_, v_b_1_);
lean_dec(v___x_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section02_powNat___boxed(lean_object* v_b_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_purelean_PureLean_NumberTheory_Section02_powNat(v_b_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec(v_b_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumUpTo(lean_object* v_x_13_){
_start:
{
lean_object* v_zero_14_; uint8_t v_isZero_15_; 
v_zero_14_ = lean_unsigned_to_nat(0u);
v_isZero_15_ = lean_nat_dec_eq(v_x_13_, v_zero_14_);
if (v_isZero_15_ == 1)
{
return v_zero_14_;
}
else
{
lean_object* v_one_16_; lean_object* v_n_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v_one_16_ = lean_unsigned_to_nat(1u);
v_n_17_ = lean_nat_sub(v_x_13_, v_one_16_);
v___x_18_ = lp_purelean_PureLean_NumberTheory_Section03_sumUpTo(v_n_17_);
v___x_19_ = lean_nat_add(v_n_17_, v_one_16_);
lean_dec(v_n_17_);
v___x_20_ = lean_nat_add(v___x_18_, v___x_19_);
lean_dec(v___x_19_);
lean_dec(v___x_18_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumUpTo___boxed(lean_object* v_x_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_purelean_PureLean_NumberTheory_Section03_sumUpTo(v_x_21_);
lean_dec(v_x_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumOdds(lean_object* v_x_23_){
_start:
{
lean_object* v_zero_24_; uint8_t v_isZero_25_; 
v_zero_24_ = lean_unsigned_to_nat(0u);
v_isZero_25_ = lean_nat_dec_eq(v_x_23_, v_zero_24_);
if (v_isZero_25_ == 1)
{
return v_zero_24_;
}
else
{
lean_object* v_one_26_; lean_object* v_n_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_one_26_ = lean_unsigned_to_nat(1u);
v_n_27_ = lean_nat_sub(v_x_23_, v_one_26_);
v___x_28_ = lp_purelean_PureLean_NumberTheory_Section03_sumOdds(v_n_27_);
v___x_29_ = lean_unsigned_to_nat(2u);
v___x_30_ = lean_nat_mul(v___x_29_, v_n_27_);
lean_dec(v_n_27_);
v___x_31_ = lean_nat_add(v___x_30_, v_one_26_);
lean_dec(v___x_30_);
v___x_32_ = lean_nat_add(v___x_28_, v___x_31_);
lean_dec(v___x_31_);
lean_dec(v___x_28_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumOdds___boxed(lean_object* v_x_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_purelean_PureLean_NumberTheory_Section03_sumOdds(v_x_33_);
lean_dec(v_x_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_pow2N(lean_object* v_x_35_){
_start:
{
lean_object* v_zero_36_; uint8_t v_isZero_37_; 
v_zero_36_ = lean_unsigned_to_nat(0u);
v_isZero_37_ = lean_nat_dec_eq(v_x_35_, v_zero_36_);
if (v_isZero_37_ == 1)
{
lean_object* v___x_38_; 
v___x_38_ = lean_unsigned_to_nat(1u);
return v___x_38_;
}
else
{
lean_object* v_one_39_; lean_object* v_n_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_one_39_ = lean_unsigned_to_nat(1u);
v_n_40_ = lean_nat_sub(v_x_35_, v_one_39_);
v___x_41_ = lean_unsigned_to_nat(2u);
v___x_42_ = lp_purelean_PureLean_NumberTheory_Section03_pow2N(v_n_40_);
lean_dec(v_n_40_);
v___x_43_ = lean_nat_mul(v___x_41_, v___x_42_);
lean_dec(v___x_42_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_pow2N___boxed(lean_object* v_x_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lp_purelean_PureLean_NumberTheory_Section03_pow2N(v_x_44_);
lean_dec(v_x_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumPow2(lean_object* v_x_46_){
_start:
{
lean_object* v_zero_47_; uint8_t v_isZero_48_; 
v_zero_47_ = lean_unsigned_to_nat(0u);
v_isZero_48_ = lean_nat_dec_eq(v_x_46_, v_zero_47_);
if (v_isZero_48_ == 1)
{
lean_object* v___x_49_; 
v___x_49_ = lean_unsigned_to_nat(1u);
return v___x_49_;
}
else
{
lean_object* v_one_50_; lean_object* v_n_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_one_50_ = lean_unsigned_to_nat(1u);
v_n_51_ = lean_nat_sub(v_x_46_, v_one_50_);
v___x_52_ = lp_purelean_PureLean_NumberTheory_Section03_sumPow2(v_n_51_);
v___x_53_ = lean_nat_add(v_n_51_, v_one_50_);
lean_dec(v_n_51_);
v___x_54_ = lp_purelean_PureLean_NumberTheory_Section03_pow2N(v___x_53_);
lean_dec(v___x_53_);
v___x_55_ = lean_nat_add(v___x_52_, v___x_54_);
lean_dec(v___x_54_);
lean_dec(v___x_52_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumPow2___boxed(lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_purelean_PureLean_NumberTheory_Section03_sumPow2(v_x_56_);
lean_dec(v_x_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_fibN(lean_object* v_x_58_){
_start:
{
lean_object* v_zero_59_; uint8_t v_isZero_60_; 
v_zero_59_ = lean_unsigned_to_nat(0u);
v_isZero_60_ = lean_nat_dec_eq(v_x_58_, v_zero_59_);
if (v_isZero_60_ == 1)
{
return v_zero_59_;
}
else
{
lean_object* v_one_61_; lean_object* v_n_62_; uint8_t v_isZero_63_; 
v_one_61_ = lean_unsigned_to_nat(1u);
v_n_62_ = lean_nat_sub(v_x_58_, v_one_61_);
v_isZero_63_ = lean_nat_dec_eq(v_n_62_, v_zero_59_);
if (v_isZero_63_ == 1)
{
lean_dec(v_n_62_);
return v_one_61_;
}
else
{
lean_object* v_n_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_n_64_ = lean_nat_sub(v_n_62_, v_one_61_);
lean_dec(v_n_62_);
v___x_65_ = lp_purelean_PureLean_NumberTheory_Section03_fibN(v_n_64_);
v___x_66_ = lean_nat_add(v_n_64_, v_one_61_);
lean_dec(v_n_64_);
v___x_67_ = lp_purelean_PureLean_NumberTheory_Section03_fibN(v___x_66_);
lean_dec(v___x_66_);
v___x_68_ = lean_nat_add(v___x_65_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v___x_65_);
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_fibN___boxed(lean_object* v_x_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = lp_purelean_PureLean_NumberTheory_Section03_fibN(v_x_69_);
lean_dec(v_x_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumFib(lean_object* v_x_71_){
_start:
{
lean_object* v_zero_72_; uint8_t v_isZero_73_; 
v_zero_72_ = lean_unsigned_to_nat(0u);
v_isZero_73_ = lean_nat_dec_eq(v_x_71_, v_zero_72_);
if (v_isZero_73_ == 1)
{
return v_zero_72_;
}
else
{
lean_object* v_one_74_; lean_object* v_n_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_one_74_ = lean_unsigned_to_nat(1u);
v_n_75_ = lean_nat_sub(v_x_71_, v_one_74_);
v___x_76_ = lp_purelean_PureLean_NumberTheory_Section03_sumFib(v_n_75_);
v___x_77_ = lean_nat_add(v_n_75_, v_one_74_);
lean_dec(v_n_75_);
v___x_78_ = lp_purelean_PureLean_NumberTheory_Section03_fibN(v___x_77_);
lean_dec(v___x_77_);
v___x_79_ = lean_nat_add(v___x_76_, v___x_78_);
lean_dec(v___x_78_);
lean_dec(v___x_76_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_NumberTheory_Section03_sumFib___boxed(lean_object* v_x_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = lp_purelean_PureLean_NumberTheory_Section03_sumFib(v_x_80_);
lean_dec(v_x_80_);
return v_res_81_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_purelean_PureLean_NumberTheory(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize_runtime_module();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
