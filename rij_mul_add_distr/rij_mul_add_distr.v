Require Import Bool.
Require Import List.
Require Import lib.
Require Import prim.
Require Import tacdef.

Require Import 
rij_mul_add_distr0  rij_mul_add_distr1  rij_mul_add_distr2  rij_mul_add_distr3  rij_mul_add_distr4  rij_mul_add_distr5  
rij_mul_add_distr6  rij_mul_add_distr7  rij_mul_add_distr8  rij_mul_add_distr9  rij_mul_add_distr10 rij_mul_add_distr11 
rij_mul_add_distr12 rij_mul_add_distr13 rij_mul_add_distr14 rij_mul_add_distr15 rij_mul_add_distr16 rij_mul_add_distr17 
rij_mul_add_distr18 rij_mul_add_distr19 rij_mul_add_distr20 rij_mul_add_distr21 rij_mul_add_distr22 rij_mul_add_distr23 
rij_mul_add_distr24 rij_mul_add_distr25 rij_mul_add_distr26 rij_mul_add_distr27 rij_mul_add_distr28 rij_mul_add_distr29 
rij_mul_add_distr30 rij_mul_add_distr31 rij_mul_add_distr32 rij_mul_add_distr33 rij_mul_add_distr34 rij_mul_add_distr35 
rij_mul_add_distr36 rij_mul_add_distr37 rij_mul_add_distr38 rij_mul_add_distr39 rij_mul_add_distr40 rij_mul_add_distr41 
rij_mul_add_distr42 rij_mul_add_distr43 rij_mul_add_distr44 rij_mul_add_distr45 rij_mul_add_distr46 rij_mul_add_distr47 
rij_mul_add_distr48 rij_mul_add_distr49 rij_mul_add_distr50 rij_mul_add_distr51 rij_mul_add_distr52 rij_mul_add_distr53 
rij_mul_add_distr54 rij_mul_add_distr55 rij_mul_add_distr56 rij_mul_add_distr57 rij_mul_add_distr58 rij_mul_add_distr59 
rij_mul_add_distr60 rij_mul_add_distr61 rij_mul_add_distr62 rij_mul_add_distr63 rij_mul_add_distr64 rij_mul_add_distr65 
rij_mul_add_distr66 rij_mul_add_distr67 rij_mul_add_distr68 rij_mul_add_distr69 rij_mul_add_distr70 rij_mul_add_distr71
rij_mul_add_distr72 rij_mul_add_distr73 rij_mul_add_distr74 rij_mul_add_distr75 rij_mul_add_distr76 rij_mul_add_distr77 
rij_mul_add_distr78 rij_mul_add_distr79 rij_mul_add_distr80 rij_mul_add_distr81 rij_mul_add_distr82 rij_mul_add_distr83 
rij_mul_add_distr84 rij_mul_add_distr85 rij_mul_add_distr86 rij_mul_add_distr87 rij_mul_add_distr88 rij_mul_add_distr89 
rij_mul_add_distr90 rij_mul_add_distr91 rij_mul_add_distr92 rij_mul_add_distr93 rij_mul_add_distr94 rij_mul_add_distr95 
rij_mul_add_distr96 rij_mul_add_distr97 rij_mul_add_distr98 rij_mul_add_distr99 rij_mul_add_distr100 rij_mul_add_distr101 
rij_mul_add_distr102 rij_mul_add_distr103 rij_mul_add_distr104 rij_mul_add_distr105 rij_mul_add_distr106 rij_mul_add_distr107 
rij_mul_add_distr108 rij_mul_add_distr109 rij_mul_add_distr110 rij_mul_add_distr111 rij_mul_add_distr112 rij_mul_add_distr113 
rij_mul_add_distr114 rij_mul_add_distr115 rij_mul_add_distr116 rij_mul_add_distr117 rij_mul_add_distr118 rij_mul_add_distr119 
rij_mul_add_distr120 rij_mul_add_distr121 rij_mul_add_distr122 rij_mul_add_distr123 rij_mul_add_distr124 rij_mul_add_distr125 
rij_mul_add_distr126 rij_mul_add_distr127 rij_mul_add_distr128 rij_mul_add_distr129 rij_mul_add_distr130 rij_mul_add_distr131 
rij_mul_add_distr132 rij_mul_add_distr133 rij_mul_add_distr134 rij_mul_add_distr135 rij_mul_add_distr136 rij_mul_add_distr137 
rij_mul_add_distr138 rij_mul_add_distr139 rij_mul_add_distr140 rij_mul_add_distr141 rij_mul_add_distr142 rij_mul_add_distr143 
rij_mul_add_distr144 rij_mul_add_distr145 rij_mul_add_distr146 rij_mul_add_distr147 rij_mul_add_distr148 rij_mul_add_distr149 
rij_mul_add_distr150 rij_mul_add_distr151 rij_mul_add_distr152 rij_mul_add_distr153 rij_mul_add_distr154 rij_mul_add_distr155 
rij_mul_add_distr156 rij_mul_add_distr157 rij_mul_add_distr158 rij_mul_add_distr159 rij_mul_add_distr160 rij_mul_add_distr161 
rij_mul_add_distr162 rij_mul_add_distr163 rij_mul_add_distr164 rij_mul_add_distr165 rij_mul_add_distr166 rij_mul_add_distr167 
rij_mul_add_distr168 rij_mul_add_distr169 rij_mul_add_distr170 rij_mul_add_distr171 rij_mul_add_distr172 rij_mul_add_distr173 
rij_mul_add_distr174 rij_mul_add_distr175 rij_mul_add_distr176 rij_mul_add_distr177 rij_mul_add_distr178 rij_mul_add_distr179 
rij_mul_add_distr180 rij_mul_add_distr181 rij_mul_add_distr182 rij_mul_add_distr183 rij_mul_add_distr184 rij_mul_add_distr185 
rij_mul_add_distr186 rij_mul_add_distr187 rij_mul_add_distr188 rij_mul_add_distr189 rij_mul_add_distr190 rij_mul_add_distr191 
rij_mul_add_distr192 rij_mul_add_distr193 rij_mul_add_distr194 rij_mul_add_distr195 rij_mul_add_distr196 rij_mul_add_distr197 
rij_mul_add_distr198 rij_mul_add_distr199 rij_mul_add_distr200 rij_mul_add_distr201 rij_mul_add_distr202 rij_mul_add_distr203 
rij_mul_add_distr204 rij_mul_add_distr205 rij_mul_add_distr206 rij_mul_add_distr207 rij_mul_add_distr208 rij_mul_add_distr209 
rij_mul_add_distr210 rij_mul_add_distr211 rij_mul_add_distr212 rij_mul_add_distr213 rij_mul_add_distr214 rij_mul_add_distr215 
rij_mul_add_distr216 rij_mul_add_distr217 rij_mul_add_distr218 rij_mul_add_distr219 rij_mul_add_distr220 rij_mul_add_distr221 
rij_mul_add_distr222 rij_mul_add_distr223 rij_mul_add_distr224 rij_mul_add_distr225 rij_mul_add_distr226 rij_mul_add_distr227 
rij_mul_add_distr228 rij_mul_add_distr229 rij_mul_add_distr230 rij_mul_add_distr231 rij_mul_add_distr232 rij_mul_add_distr233 
rij_mul_add_distr234 rij_mul_add_distr235 rij_mul_add_distr236 rij_mul_add_distr237 rij_mul_add_distr238 rij_mul_add_distr239 
rij_mul_add_distr240 rij_mul_add_distr241 rij_mul_add_distr242 rij_mul_add_distr243 rij_mul_add_distr244 rij_mul_add_distr245 
rij_mul_add_distr246 rij_mul_add_distr247 rij_mul_add_distr248 rij_mul_add_distr249 rij_mul_add_distr250 rij_mul_add_distr251 
rij_mul_add_distr252 rij_mul_add_distr253 rij_mul_add_distr254 rij_mul_add_distr255.


Lemma rij_mul_add_distr : forall a b c : Poly,
  length a = 8 -> length b = 8 -> length c = 8 ->
  rij_mul (rij_add a b) c = rij_add (rij_mul a c) (rij_mul b c).
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
  apply rij_mul_add_distr255;auto. apply rij_mul_add_distr254;auto. apply rij_mul_add_distr253;auto.
  apply rij_mul_add_distr252;auto. apply rij_mul_add_distr251;auto. apply rij_mul_add_distr250;auto.
  apply rij_mul_add_distr249;auto. apply rij_mul_add_distr248;auto. apply rij_mul_add_distr247;auto.
  apply rij_mul_add_distr246;auto. apply rij_mul_add_distr245;auto. apply rij_mul_add_distr244;auto.
  apply rij_mul_add_distr243;auto. apply rij_mul_add_distr242;auto. apply rij_mul_add_distr241;auto.
  apply rij_mul_add_distr240;auto. apply rij_mul_add_distr239;auto. apply rij_mul_add_distr238;auto.
  apply rij_mul_add_distr237;auto. apply rij_mul_add_distr236;auto. apply rij_mul_add_distr235;auto.
  apply rij_mul_add_distr234;auto. apply rij_mul_add_distr233;auto. apply rij_mul_add_distr232;auto.
  apply rij_mul_add_distr231;auto. apply rij_mul_add_distr230;auto. apply rij_mul_add_distr229;auto.
  apply rij_mul_add_distr228;auto. apply rij_mul_add_distr227;auto. apply rij_mul_add_distr226;auto.
  apply rij_mul_add_distr225;auto. apply rij_mul_add_distr224;auto. apply rij_mul_add_distr223;auto.
  apply rij_mul_add_distr222;auto. apply rij_mul_add_distr221;auto. apply rij_mul_add_distr220;auto.
  apply rij_mul_add_distr219;auto. apply rij_mul_add_distr218;auto. apply rij_mul_add_distr217;auto.
  apply rij_mul_add_distr216;auto. apply rij_mul_add_distr215;auto. apply rij_mul_add_distr214;auto.
  apply rij_mul_add_distr213;auto. apply rij_mul_add_distr212;auto. apply rij_mul_add_distr211;auto.
  apply rij_mul_add_distr210;auto. apply rij_mul_add_distr209;auto. apply rij_mul_add_distr208;auto.
  apply rij_mul_add_distr207;auto. apply rij_mul_add_distr206;auto. apply rij_mul_add_distr205;auto.
  apply rij_mul_add_distr204;auto. apply rij_mul_add_distr203;auto. apply rij_mul_add_distr202;auto.
  apply rij_mul_add_distr201;auto. apply rij_mul_add_distr200;auto. apply rij_mul_add_distr199;auto.
  apply rij_mul_add_distr198;auto. apply rij_mul_add_distr197;auto. apply rij_mul_add_distr196;auto.
  apply rij_mul_add_distr195;auto. apply rij_mul_add_distr194;auto. apply rij_mul_add_distr193;auto.
  apply rij_mul_add_distr192;auto. apply rij_mul_add_distr191;auto. apply rij_mul_add_distr190;auto.
  apply rij_mul_add_distr189;auto. apply rij_mul_add_distr188;auto. apply rij_mul_add_distr187;auto.
  apply rij_mul_add_distr186;auto. apply rij_mul_add_distr185;auto. apply rij_mul_add_distr184;auto.
  apply rij_mul_add_distr183;auto. apply rij_mul_add_distr182;auto. apply rij_mul_add_distr181;auto.
  apply rij_mul_add_distr180;auto. apply rij_mul_add_distr179;auto. apply rij_mul_add_distr178;auto.
  apply rij_mul_add_distr177;auto. apply rij_mul_add_distr176;auto. apply rij_mul_add_distr175;auto.
  apply rij_mul_add_distr174;auto. apply rij_mul_add_distr173;auto. apply rij_mul_add_distr172;auto.
  apply rij_mul_add_distr171;auto. apply rij_mul_add_distr170;auto. apply rij_mul_add_distr169;auto.
  apply rij_mul_add_distr168;auto. apply rij_mul_add_distr167;auto. apply rij_mul_add_distr166;auto.
  apply rij_mul_add_distr165;auto. apply rij_mul_add_distr164;auto. apply rij_mul_add_distr163;auto.
  apply rij_mul_add_distr162;auto. apply rij_mul_add_distr161;auto. apply rij_mul_add_distr160;auto.
  apply rij_mul_add_distr159;auto. apply rij_mul_add_distr158;auto. apply rij_mul_add_distr157;auto.
  apply rij_mul_add_distr156;auto. apply rij_mul_add_distr155;auto. apply rij_mul_add_distr154;auto.
  apply rij_mul_add_distr153;auto. apply rij_mul_add_distr152;auto. apply rij_mul_add_distr151;auto.
  apply rij_mul_add_distr150;auto. apply rij_mul_add_distr149;auto. apply rij_mul_add_distr148;auto.
  apply rij_mul_add_distr147;auto. apply rij_mul_add_distr146;auto. apply rij_mul_add_distr145;auto.
  apply rij_mul_add_distr144;auto. apply rij_mul_add_distr143;auto. apply rij_mul_add_distr142;auto.
  apply rij_mul_add_distr141;auto. apply rij_mul_add_distr140;auto. apply rij_mul_add_distr139;auto.
  apply rij_mul_add_distr138;auto. apply rij_mul_add_distr137;auto. apply rij_mul_add_distr136;auto.
  apply rij_mul_add_distr135;auto. apply rij_mul_add_distr134;auto. apply rij_mul_add_distr133;auto.
  apply rij_mul_add_distr132;auto. apply rij_mul_add_distr131;auto. apply rij_mul_add_distr130;auto.
  apply rij_mul_add_distr129;auto. apply rij_mul_add_distr128;auto. apply rij_mul_add_distr127;auto.
  apply rij_mul_add_distr126;auto. apply rij_mul_add_distr125;auto. apply rij_mul_add_distr124;auto.
  apply rij_mul_add_distr123;auto. apply rij_mul_add_distr122;auto. apply rij_mul_add_distr121;auto.
  apply rij_mul_add_distr120;auto. apply rij_mul_add_distr119;auto. apply rij_mul_add_distr118;auto.
  apply rij_mul_add_distr117;auto. apply rij_mul_add_distr116;auto. apply rij_mul_add_distr115;auto.
  apply rij_mul_add_distr114;auto. apply rij_mul_add_distr113;auto. apply rij_mul_add_distr112;auto.
  apply rij_mul_add_distr111;auto. apply rij_mul_add_distr110;auto. apply rij_mul_add_distr109;auto.
  apply rij_mul_add_distr108;auto. apply rij_mul_add_distr107;auto. apply rij_mul_add_distr106;auto.
  apply rij_mul_add_distr105;auto. apply rij_mul_add_distr104;auto. apply rij_mul_add_distr103;auto.
  apply rij_mul_add_distr102;auto. apply rij_mul_add_distr101;auto. apply rij_mul_add_distr100;auto.
  apply rij_mul_add_distr99;auto. apply rij_mul_add_distr98;auto. apply rij_mul_add_distr97;auto.
  apply rij_mul_add_distr96;auto. apply rij_mul_add_distr95;auto. apply rij_mul_add_distr94;auto.
  apply rij_mul_add_distr93;auto. apply rij_mul_add_distr92;auto. apply rij_mul_add_distr91;auto.
  apply rij_mul_add_distr90;auto. apply rij_mul_add_distr89;auto. apply rij_mul_add_distr88;auto.
  apply rij_mul_add_distr87;auto. apply rij_mul_add_distr86;auto. apply rij_mul_add_distr85;auto.
  apply rij_mul_add_distr84;auto. apply rij_mul_add_distr83;auto. apply rij_mul_add_distr82;auto.
  apply rij_mul_add_distr81;auto. apply rij_mul_add_distr80;auto. apply rij_mul_add_distr79;auto.
  apply rij_mul_add_distr78;auto. apply rij_mul_add_distr77;auto. apply rij_mul_add_distr76;auto.
  apply rij_mul_add_distr75;auto. apply rij_mul_add_distr74;auto. apply rij_mul_add_distr73;auto.
  apply rij_mul_add_distr72;auto. apply rij_mul_add_distr71;auto. apply rij_mul_add_distr70;auto.
  apply rij_mul_add_distr69;auto. apply rij_mul_add_distr68;auto. apply rij_mul_add_distr67;auto.
  apply rij_mul_add_distr66;auto. apply rij_mul_add_distr65;auto. apply rij_mul_add_distr64;auto.
  apply rij_mul_add_distr63;auto. apply rij_mul_add_distr62;auto. apply rij_mul_add_distr61;auto.
  apply rij_mul_add_distr60;auto. apply rij_mul_add_distr59;auto. apply rij_mul_add_distr58;auto.
  apply rij_mul_add_distr57;auto. apply rij_mul_add_distr56;auto. apply rij_mul_add_distr55;auto.
  apply rij_mul_add_distr54;auto. apply rij_mul_add_distr53;auto. apply rij_mul_add_distr52;auto.
  apply rij_mul_add_distr51;auto. apply rij_mul_add_distr50;auto. apply rij_mul_add_distr49;auto.
  apply rij_mul_add_distr48;auto. apply rij_mul_add_distr47;auto. apply rij_mul_add_distr46;auto.
  apply rij_mul_add_distr45;auto. apply rij_mul_add_distr44;auto. apply rij_mul_add_distr43;auto.
  apply rij_mul_add_distr42;auto. apply rij_mul_add_distr41;auto. apply rij_mul_add_distr40;auto.
  apply rij_mul_add_distr39;auto. apply rij_mul_add_distr38;auto. apply rij_mul_add_distr37;auto.
  apply rij_mul_add_distr36;auto. apply rij_mul_add_distr35;auto. apply rij_mul_add_distr34;auto.
  apply rij_mul_add_distr33;auto. apply rij_mul_add_distr32;auto. apply rij_mul_add_distr31;auto.
  apply rij_mul_add_distr30;auto. apply rij_mul_add_distr29;auto. apply rij_mul_add_distr28;auto.
  apply rij_mul_add_distr27;auto. apply rij_mul_add_distr26;auto. apply rij_mul_add_distr25;auto.
  apply rij_mul_add_distr24;auto. apply rij_mul_add_distr23;auto. apply rij_mul_add_distr22;auto.
  apply rij_mul_add_distr21;auto. apply rij_mul_add_distr20;auto. apply rij_mul_add_distr19;auto.
  apply rij_mul_add_distr18;auto. apply rij_mul_add_distr17;auto. apply rij_mul_add_distr16;auto.
  apply rij_mul_add_distr15;auto. apply rij_mul_add_distr14;auto. apply rij_mul_add_distr13;auto.
  apply rij_mul_add_distr12;auto. apply rij_mul_add_distr11;auto. apply rij_mul_add_distr10;auto.
  apply rij_mul_add_distr9;auto.  apply rij_mul_add_distr8;auto.  apply rij_mul_add_distr7;auto.
  apply rij_mul_add_distr6;auto.  apply rij_mul_add_distr5;auto.  apply rij_mul_add_distr4;auto.
  apply rij_mul_add_distr3;auto.  apply rij_mul_add_distr2;auto.  apply rij_mul_add_distr1;auto.
  apply rij_mul_add_distr0;auto.
Qed.






























