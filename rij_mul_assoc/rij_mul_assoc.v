Require Import Bool.
Require Import List.
Require Import lib.
Require Import prim.
Require Import tacdef.

Require Import 
rij_mul_assoc0   rij_mul_assoc1   rij_mul_assoc2   rij_mul_assoc3   rij_mul_assoc4   rij_mul_assoc5  
rij_mul_assoc6   rij_mul_assoc7   rij_mul_assoc8   rij_mul_assoc9   rij_mul_assoc10  rij_mul_assoc11 
rij_mul_assoc12  rij_mul_assoc13  rij_mul_assoc14  rij_mul_assoc15  rij_mul_assoc16  rij_mul_assoc17 
rij_mul_assoc18  rij_mul_assoc19  rij_mul_assoc20  rij_mul_assoc21  rij_mul_assoc22  rij_mul_assoc23 
rij_mul_assoc24  rij_mul_assoc25  rij_mul_assoc26  rij_mul_assoc27  rij_mul_assoc28  rij_mul_assoc29 
rij_mul_assoc30  rij_mul_assoc31  rij_mul_assoc32  rij_mul_assoc33  rij_mul_assoc34  rij_mul_assoc35 
rij_mul_assoc36  rij_mul_assoc37  rij_mul_assoc38  rij_mul_assoc39  rij_mul_assoc40  rij_mul_assoc41 
rij_mul_assoc42  rij_mul_assoc43  rij_mul_assoc44  rij_mul_assoc45  rij_mul_assoc46  rij_mul_assoc47 
rij_mul_assoc48  rij_mul_assoc49  rij_mul_assoc50  rij_mul_assoc51  rij_mul_assoc52  rij_mul_assoc53 
rij_mul_assoc54  rij_mul_assoc55  rij_mul_assoc56  rij_mul_assoc57  rij_mul_assoc58  rij_mul_assoc59 
rij_mul_assoc60  rij_mul_assoc61  rij_mul_assoc62  rij_mul_assoc63  rij_mul_assoc64  rij_mul_assoc65 
rij_mul_assoc66  rij_mul_assoc67  rij_mul_assoc68  rij_mul_assoc69  rij_mul_assoc70  rij_mul_assoc71
rij_mul_assoc72  rij_mul_assoc73  rij_mul_assoc74  rij_mul_assoc75  rij_mul_assoc76  rij_mul_assoc77 
rij_mul_assoc78  rij_mul_assoc79  rij_mul_assoc80  rij_mul_assoc81  rij_mul_assoc82  rij_mul_assoc83 
rij_mul_assoc84  rij_mul_assoc85  rij_mul_assoc86  rij_mul_assoc87  rij_mul_assoc88  rij_mul_assoc89 
rij_mul_assoc90  rij_mul_assoc91  rij_mul_assoc92  rij_mul_assoc93  rij_mul_assoc94  rij_mul_assoc95 
rij_mul_assoc96  rij_mul_assoc97  rij_mul_assoc98  rij_mul_assoc99  rij_mul_assoc100 rij_mul_assoc101 
rij_mul_assoc102 rij_mul_assoc103 rij_mul_assoc104 rij_mul_assoc105 rij_mul_assoc106 rij_mul_assoc107 
rij_mul_assoc108 rij_mul_assoc109 rij_mul_assoc110 rij_mul_assoc111 rij_mul_assoc112 rij_mul_assoc113 
rij_mul_assoc114 rij_mul_assoc115 rij_mul_assoc116 rij_mul_assoc117 rij_mul_assoc118 rij_mul_assoc119 
rij_mul_assoc120 rij_mul_assoc121 rij_mul_assoc122 rij_mul_assoc123 rij_mul_assoc124 rij_mul_assoc125 
rij_mul_assoc126 rij_mul_assoc127 rij_mul_assoc128 rij_mul_assoc129 rij_mul_assoc130 rij_mul_assoc131 
rij_mul_assoc132 rij_mul_assoc133 rij_mul_assoc134 rij_mul_assoc135 rij_mul_assoc136 rij_mul_assoc137 
rij_mul_assoc138 rij_mul_assoc139 rij_mul_assoc140 rij_mul_assoc141 rij_mul_assoc142 rij_mul_assoc143 
rij_mul_assoc144 rij_mul_assoc145 rij_mul_assoc146 rij_mul_assoc147 rij_mul_assoc148 rij_mul_assoc149 
rij_mul_assoc150 rij_mul_assoc151 rij_mul_assoc152 rij_mul_assoc153 rij_mul_assoc154 rij_mul_assoc155 
rij_mul_assoc156 rij_mul_assoc157 rij_mul_assoc158 rij_mul_assoc159 rij_mul_assoc160 rij_mul_assoc161 
rij_mul_assoc162 rij_mul_assoc163 rij_mul_assoc164 rij_mul_assoc165 rij_mul_assoc166 rij_mul_assoc167 
rij_mul_assoc168 rij_mul_assoc169 rij_mul_assoc170 rij_mul_assoc171 rij_mul_assoc172 rij_mul_assoc173 
rij_mul_assoc174 rij_mul_assoc175 rij_mul_assoc176 rij_mul_assoc177 rij_mul_assoc178 rij_mul_assoc179 
rij_mul_assoc180 rij_mul_assoc181 rij_mul_assoc182 rij_mul_assoc183 rij_mul_assoc184 rij_mul_assoc185 
rij_mul_assoc186 rij_mul_assoc187 rij_mul_assoc188 rij_mul_assoc189 rij_mul_assoc190 rij_mul_assoc191 
rij_mul_assoc192 rij_mul_assoc193 rij_mul_assoc194 rij_mul_assoc195 rij_mul_assoc196 rij_mul_assoc197 
rij_mul_assoc198 rij_mul_assoc199 rij_mul_assoc200 rij_mul_assoc201 rij_mul_assoc202 rij_mul_assoc203 
rij_mul_assoc204 rij_mul_assoc205 rij_mul_assoc206 rij_mul_assoc207 rij_mul_assoc208 rij_mul_assoc209 
rij_mul_assoc210 rij_mul_assoc211 rij_mul_assoc212 rij_mul_assoc213 rij_mul_assoc214 rij_mul_assoc215 
rij_mul_assoc216 rij_mul_assoc217 rij_mul_assoc218 rij_mul_assoc219 rij_mul_assoc220 rij_mul_assoc221 
rij_mul_assoc222 rij_mul_assoc223 rij_mul_assoc224 rij_mul_assoc225 rij_mul_assoc226 rij_mul_assoc227 
rij_mul_assoc228 rij_mul_assoc229 rij_mul_assoc230 rij_mul_assoc231 rij_mul_assoc232 rij_mul_assoc233 
rij_mul_assoc234 rij_mul_assoc235 rij_mul_assoc236 rij_mul_assoc237 rij_mul_assoc238 rij_mul_assoc239 
rij_mul_assoc240 rij_mul_assoc241 rij_mul_assoc242 rij_mul_assoc243 rij_mul_assoc244 rij_mul_assoc245 
rij_mul_assoc246 rij_mul_assoc247 rij_mul_assoc248 rij_mul_assoc249 rij_mul_assoc250 rij_mul_assoc251 
rij_mul_assoc252 rij_mul_assoc253 rij_mul_assoc254 rij_mul_assoc255.

Lemma rij_mul_assoc : forall (a b c : Poly),
  length a = 8 -> length b = 8 -> length c = 8 ->
  rij_mul a (rij_mul b c)  = rij_mul (rij_mul a b) c.
Proof.
  intros a b c Ha Hb Hc; apply length8 in Ha; apply length8 in Hb; apply length8 in Hc;
  destruct Ha as [a0 H0]; destruct H0 as [a1 H1]; destruct H1 as [a2 H2]; destruct H2 as [a3 H3];
  destruct H3 as [a4 H4]; destruct H4 as [a5 H5]; destruct H5 as [a6 H6]; destruct H6 as [a7 Ha7];
  destruct Hb as [b0 Hb]; destruct Hb as [b1 Hb1]; destruct Hb1 as [b2 Hb2]; destruct Hb2 as [b3 Hb3];
  destruct Hb3 as [b4 Hb4]; destruct Hb4 as [b5 Hb5]; destruct Hb5 as [b6 Hb6]; destruct Hb6 as [b7 Hb7];
  destruct Hc as [c0 Hcc]; destruct Hcc as [c1 Hc1]; destruct Hc1 as [c2 Hc2]; destruct Hc2 as [c3 Hc3];
  destruct Hc3 as [c4 Hc4]; destruct Hc4 as [c5 Hc5]; destruct Hc5 as [c6 Hc6]; destruct Hc6 as [c7 Hc7];
  rewrite Ha7,Hb7,Hc7;
  case c0;case c1;case c2;case c3;case c4;case c5;case c6;case c7.
  apply rij_mul_assoc255;auto. apply rij_mul_assoc254;auto. apply rij_mul_assoc253;auto.
  apply rij_mul_assoc252;auto. apply rij_mul_assoc251;auto. apply rij_mul_assoc250;auto.
  apply rij_mul_assoc249;auto. apply rij_mul_assoc248;auto. apply rij_mul_assoc247;auto.
  apply rij_mul_assoc246;auto. apply rij_mul_assoc245;auto. apply rij_mul_assoc244;auto.
  apply rij_mul_assoc243;auto. apply rij_mul_assoc242;auto. apply rij_mul_assoc241;auto.
  apply rij_mul_assoc240;auto. apply rij_mul_assoc239;auto. apply rij_mul_assoc238;auto.
  apply rij_mul_assoc237;auto. apply rij_mul_assoc236;auto. apply rij_mul_assoc235;auto.
  apply rij_mul_assoc234;auto. apply rij_mul_assoc233;auto. apply rij_mul_assoc232;auto.
  apply rij_mul_assoc231;auto. apply rij_mul_assoc230;auto. apply rij_mul_assoc229;auto.
  apply rij_mul_assoc228;auto. apply rij_mul_assoc227;auto. apply rij_mul_assoc226;auto.
  apply rij_mul_assoc225;auto. apply rij_mul_assoc224;auto. apply rij_mul_assoc223;auto.
  apply rij_mul_assoc222;auto. apply rij_mul_assoc221;auto. apply rij_mul_assoc220;auto.
  apply rij_mul_assoc219;auto. apply rij_mul_assoc218;auto. apply rij_mul_assoc217;auto.
  apply rij_mul_assoc216;auto. apply rij_mul_assoc215;auto. apply rij_mul_assoc214;auto.
  apply rij_mul_assoc213;auto. apply rij_mul_assoc212;auto. apply rij_mul_assoc211;auto.
  apply rij_mul_assoc210;auto. apply rij_mul_assoc209;auto. apply rij_mul_assoc208;auto.
  apply rij_mul_assoc207;auto. apply rij_mul_assoc206;auto. apply rij_mul_assoc205;auto.
  apply rij_mul_assoc204;auto. apply rij_mul_assoc203;auto. apply rij_mul_assoc202;auto.
  apply rij_mul_assoc201;auto. apply rij_mul_assoc200;auto. apply rij_mul_assoc199;auto.
  apply rij_mul_assoc198;auto. apply rij_mul_assoc197;auto. apply rij_mul_assoc196;auto.
  apply rij_mul_assoc195;auto. apply rij_mul_assoc194;auto. apply rij_mul_assoc193;auto.
  apply rij_mul_assoc192;auto. apply rij_mul_assoc191;auto. apply rij_mul_assoc190;auto.
  apply rij_mul_assoc189;auto. apply rij_mul_assoc188;auto. apply rij_mul_assoc187;auto.
  apply rij_mul_assoc186;auto. apply rij_mul_assoc185;auto. apply rij_mul_assoc184;auto.
  apply rij_mul_assoc183;auto. apply rij_mul_assoc182;auto. apply rij_mul_assoc181;auto.
  apply rij_mul_assoc180;auto. apply rij_mul_assoc179;auto. apply rij_mul_assoc178;auto.
  apply rij_mul_assoc177;auto. apply rij_mul_assoc176;auto. apply rij_mul_assoc175;auto.
  apply rij_mul_assoc174;auto. apply rij_mul_assoc173;auto. apply rij_mul_assoc172;auto.
  apply rij_mul_assoc171;auto. apply rij_mul_assoc170;auto. apply rij_mul_assoc169;auto.
  apply rij_mul_assoc168;auto. apply rij_mul_assoc167;auto. apply rij_mul_assoc166;auto.
  apply rij_mul_assoc165;auto. apply rij_mul_assoc164;auto. apply rij_mul_assoc163;auto.
  apply rij_mul_assoc162;auto. apply rij_mul_assoc161;auto. apply rij_mul_assoc160;auto.
  apply rij_mul_assoc159;auto. apply rij_mul_assoc158;auto. apply rij_mul_assoc157;auto.
  apply rij_mul_assoc156;auto. apply rij_mul_assoc155;auto. apply rij_mul_assoc154;auto.
  apply rij_mul_assoc153;auto. apply rij_mul_assoc152;auto. apply rij_mul_assoc151;auto.
  apply rij_mul_assoc150;auto. apply rij_mul_assoc149;auto. apply rij_mul_assoc148;auto.
  apply rij_mul_assoc147;auto. apply rij_mul_assoc146;auto. apply rij_mul_assoc145;auto.
  apply rij_mul_assoc144;auto. apply rij_mul_assoc143;auto. apply rij_mul_assoc142;auto.
  apply rij_mul_assoc141;auto. apply rij_mul_assoc140;auto. apply rij_mul_assoc139;auto.
  apply rij_mul_assoc138;auto. apply rij_mul_assoc137;auto. apply rij_mul_assoc136;auto.
  apply rij_mul_assoc135;auto. apply rij_mul_assoc134;auto. apply rij_mul_assoc133;auto.
  apply rij_mul_assoc132;auto. apply rij_mul_assoc131;auto. apply rij_mul_assoc130;auto.
  apply rij_mul_assoc129;auto. apply rij_mul_assoc128;auto. apply rij_mul_assoc127;auto.
  apply rij_mul_assoc126;auto. apply rij_mul_assoc125;auto. apply rij_mul_assoc124;auto.
  apply rij_mul_assoc123;auto. apply rij_mul_assoc122;auto. apply rij_mul_assoc121;auto.
  apply rij_mul_assoc120;auto. apply rij_mul_assoc119;auto. apply rij_mul_assoc118;auto.
  apply rij_mul_assoc117;auto. apply rij_mul_assoc116;auto. apply rij_mul_assoc115;auto.
  apply rij_mul_assoc114;auto. apply rij_mul_assoc113;auto. apply rij_mul_assoc112;auto.
  apply rij_mul_assoc111;auto. apply rij_mul_assoc110;auto. apply rij_mul_assoc109;auto.
  apply rij_mul_assoc108;auto. apply rij_mul_assoc107;auto. apply rij_mul_assoc106;auto.
  apply rij_mul_assoc105;auto. apply rij_mul_assoc104;auto. apply rij_mul_assoc103;auto.
  apply rij_mul_assoc102;auto. apply rij_mul_assoc101;auto. apply rij_mul_assoc100;auto.
  apply rij_mul_assoc99;auto. apply rij_mul_assoc98;auto. apply rij_mul_assoc97;auto.
  apply rij_mul_assoc96;auto. apply rij_mul_assoc95;auto. apply rij_mul_assoc94;auto.
  apply rij_mul_assoc93;auto. apply rij_mul_assoc92;auto. apply rij_mul_assoc91;auto.
  apply rij_mul_assoc90;auto. apply rij_mul_assoc89;auto. apply rij_mul_assoc88;auto.
  apply rij_mul_assoc87;auto. apply rij_mul_assoc86;auto. apply rij_mul_assoc85;auto.
  apply rij_mul_assoc84;auto. apply rij_mul_assoc83;auto. apply rij_mul_assoc82;auto.
  apply rij_mul_assoc81;auto. apply rij_mul_assoc80;auto. apply rij_mul_assoc79;auto.
  apply rij_mul_assoc78;auto. apply rij_mul_assoc77;auto. apply rij_mul_assoc76;auto.
  apply rij_mul_assoc75;auto. apply rij_mul_assoc74;auto. apply rij_mul_assoc73;auto.
  apply rij_mul_assoc72;auto. apply rij_mul_assoc71;auto. apply rij_mul_assoc70;auto.
  apply rij_mul_assoc69;auto. apply rij_mul_assoc68;auto. apply rij_mul_assoc67;auto.
  apply rij_mul_assoc66;auto. apply rij_mul_assoc65;auto. apply rij_mul_assoc64;auto.
  apply rij_mul_assoc63;auto. apply rij_mul_assoc62;auto. apply rij_mul_assoc61;auto.
  apply rij_mul_assoc60;auto. apply rij_mul_assoc59;auto. apply rij_mul_assoc58;auto.
  apply rij_mul_assoc57;auto. apply rij_mul_assoc56;auto. apply rij_mul_assoc55;auto.
  apply rij_mul_assoc54;auto. apply rij_mul_assoc53;auto. apply rij_mul_assoc52;auto.
  apply rij_mul_assoc51;auto. apply rij_mul_assoc50;auto. apply rij_mul_assoc49;auto.
  apply rij_mul_assoc48;auto. apply rij_mul_assoc47;auto. apply rij_mul_assoc46;auto.
  apply rij_mul_assoc45;auto. apply rij_mul_assoc44;auto. apply rij_mul_assoc43;auto.
  apply rij_mul_assoc42;auto. apply rij_mul_assoc41;auto. apply rij_mul_assoc40;auto.
  apply rij_mul_assoc39;auto. apply rij_mul_assoc38;auto. apply rij_mul_assoc37;auto.
  apply rij_mul_assoc36;auto. apply rij_mul_assoc35;auto. apply rij_mul_assoc34;auto.
  apply rij_mul_assoc33;auto. apply rij_mul_assoc32;auto. apply rij_mul_assoc31;auto.
  apply rij_mul_assoc30;auto. apply rij_mul_assoc29;auto. apply rij_mul_assoc28;auto.
  apply rij_mul_assoc27;auto. apply rij_mul_assoc26;auto. apply rij_mul_assoc25;auto.
  apply rij_mul_assoc24;auto. apply rij_mul_assoc23;auto. apply rij_mul_assoc22;auto.
  apply rij_mul_assoc21;auto. apply rij_mul_assoc20;auto. apply rij_mul_assoc19;auto.
  apply rij_mul_assoc18;auto. apply rij_mul_assoc17;auto. apply rij_mul_assoc16;auto.
  apply rij_mul_assoc15;auto. apply rij_mul_assoc14;auto. apply rij_mul_assoc13;auto.
  apply rij_mul_assoc12;auto. apply rij_mul_assoc11;auto. apply rij_mul_assoc10;auto.
  apply rij_mul_assoc9;auto.  apply rij_mul_assoc8;auto.  apply rij_mul_assoc7;auto.
  apply rij_mul_assoc6;auto.  apply rij_mul_assoc5;auto.  apply rij_mul_assoc4;auto.
  apply rij_mul_assoc3;auto.  apply rij_mul_assoc2;auto.  apply rij_mul_assoc1;auto.
  apply rij_mul_assoc0;auto.
Qed.

























