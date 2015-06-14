open Format
open Syntax
open Support.Error
open Support.Pervasive
open Range

(* ------------------------   EVALUATION  ------------------------ *)

exception NoRuleApplies

let rec isnumericval ctx t = match t with
    TmZero(_) -> true
  | TmSucc(_,t1) -> isnumericval ctx t1
  | _ -> false

let rec isval ctx t = match t with
    TmTrue(_)  -> true
  | TmFalse(_) -> true
  | TmString _  -> true
  | TmUnit(_)  -> true
  | TmFloat _  -> true
  | t when isnumericval ctx t  -> true
  | TmAbs(_,_,_,_) -> true
  | TmRecord(_,fields) -> List.for_all (fun (l,ti) -> isval ctx ti) fields
  | TmInt(_,_) -> true
  | _ -> false

let rec eval1 ctx t = match t with
    TmApp(_,TmError(fi),t2) ->
      TmError(fi)
  | TmApp(_,v1,TmError(fi)) when isval ctx v1 ->
      TmError(fi)
  | TmApp(fi,TmAbs(_,x,tyT11,t12),v2) when isval ctx v2 ->
      termSubstTop v2 t12
  | TmApp(fi,v1,t2) when isval ctx v1 ->
      let t2' = eval1 ctx t2 in
      TmApp(fi, v1, t2')
  | TmApp(fi,t1,t2) ->
      let t1' = eval1 ctx t1 in
      TmApp(fi, t1', t2)
  | TmIf(_,TmTrue(_),t2,t3) ->
      t2
  | TmIf(_,TmFalse(_),t2,t3) ->
      t3
  | TmIf(_,TmError(fi),t2,t3) ->
      TmError(fi)
  | TmIf(fi,t1,t2,t3) ->
      let t1' = eval1 ctx t1 in
      TmIf(fi, t1', t2, t3)
  | TmRecord(fi,fields) ->
      let rec evalafield l = match l with 
        [] -> raise NoRuleApplies
      | (l,vi)::rest when isval ctx vi -> 
          let rest' = evalafield rest in
          (l,vi)::rest'
      | (l,ti)::rest -> 
          let ti' = eval1 ctx ti in
          (l, ti')::rest
      in let fields' = evalafield fields in
      TmRecord(fi, fields')
  | TmProj(fi, (TmRecord(_, fields) as v1), l) when isval ctx v1 ->
      (try List.assoc l fields
       with Not_found -> raise NoRuleApplies)
  | TmProj(fi, t1, l) ->
      let t1' = eval1 ctx t1 in
      TmProj(fi, t1', l)
  | TmLet(fi,x,v1,t2) when isval ctx v1 ->
      termSubstTop v1 t2 
  | TmLet(fi,x,t1,t2) ->
      let t1' = eval1 ctx t1 in
      TmLet(fi, x, t1', t2) 
  | TmFix(fi,v1) as t when isval ctx v1 ->
      (match v1 with
         TmAbs(_,_,_,t12) -> termSubstTop t t12
       | _ -> raise NoRuleApplies)
  | TmFix(fi,t1) ->
      let t1' = eval1 ctx t1
      in TmFix(fi,t1')
  | TmVar(fi,n,_) ->
      (match getbinding fi ctx n with
          TmAbbBind(t,_) -> t 
        | _ -> raise NoRuleApplies)
  | TmAscribe(fi,v1,tyT) when isval ctx v1 ->
      v1
  | TmAscribe(fi,t1,tyT) ->
      let t1' = eval1 ctx t1 in
      TmAscribe(fi,t1',tyT)
  | TmTimesfloat(fi,TmFloat(_,f1),TmFloat(_,f2)) ->
      TmFloat(fi, f1 *. f2)
  | TmTimesfloat(fi,(TmFloat(_,f1) as t1),t2) ->
      let t2' = eval1 ctx t2 in
      TmTimesfloat(fi,t1,t2') 
  | TmTimesfloat(fi,t1,t2) ->
      let t1' = eval1 ctx t1 in
      TmTimesfloat(fi,t1',t2) 
  | TmSucc(fi,t1) ->
      let t1' = eval1 ctx t1 in
      TmSucc(fi, t1')
  | TmPred(_,TmZero(_)) ->
      TmZero(dummyinfo)
  | TmPred(_,TmSucc(_,nv1)) when (isnumericval ctx nv1) ->
      nv1
  | TmPred(fi,t1) ->
      let t1' = eval1 ctx t1 in
      TmPred(fi, t1')
  | TmIsZero(_,TmZero(_)) ->
      TmTrue(dummyinfo)
  | TmIsZero(_,TmSucc(_,nv1)) when (isnumericval ctx nv1) ->
      TmFalse(dummyinfo)
  | TmIsZero(fi,t1) ->
      let t1' = eval1 ctx t1 in
      TmIsZero(fi, t1')
  | TmPlus(fi,TmInt(_,num1),TmInt(_,num2)) -> 
      TmInt(fi,num1 + num2)
  | TmPlus(fi,TmInt(fi2,num1),t2) ->
      TmPlus(fi,TmInt(fi2,num1), eval1 ctx t2)
  | TmPlus(fi,t1,t2) ->
      TmPlus(fi, eval1 ctx t1, t2)
  | TmMinus(fi,TmInt(_,num1),TmInt(_,num2)) ->
      TmInt(fi,num1 - num2)
  | TmMinus(fi,TmInt(fi2,num1),t2) ->
      TmMinus(fi,TmInt(fi2,num1), eval1 ctx t2)
  | TmMinus(fi,t1,t2) ->
      TmMinus(fi, eval1 ctx t1, t2)
  | TmGreater(fi,TmInt(_,num1),TmInt(_,num2)) ->
      if num1 > num2 then TmTrue(dummyinfo)
      else TmFalse(dummyinfo)
  | TmGreater(fi,TmInt(fi2,num1),t2) ->
      TmGreater(fi,TmInt(fi2,num1), eval1 ctx t2)
  | TmGreater(fi,t1,t2) ->
      TmGreater(fi, eval1 ctx t1, t2)
  | TmGreaterEqual(fi,TmInt(_,num1),TmInt(_,num2)) ->
      if num1 >= num2 then TmTrue(dummyinfo)
      else TmFalse(dummyinfo)
  | TmGreaterEqual(fi,TmInt(fi2,num1),t2) ->
      TmGreaterEqual(fi,TmInt(fi2,num1), eval1 ctx t2)
  | TmGreaterEqual(fi,t1,t2) ->
      TmGreaterEqual(fi, eval1 ctx t1, t2)
  | TmLess(fi,TmInt(_,num1),TmInt(_,num2)) ->
      if num1 < num2 then TmTrue(dummyinfo)
      else TmFalse(dummyinfo)
  | TmLess(fi,TmInt(fi2,num1),t2) ->
      TmLess(fi,TmInt(fi2,num1), eval1 ctx t2)
  | TmLess(fi,t1,t2) ->
      TmLess(fi, eval1 ctx t1, t2)
  | TmLessEqual(fi,TmInt(_,num1),TmInt(_,num2)) ->
      if num1 <= num2 then TmTrue(dummyinfo)
      else TmFalse(dummyinfo)
  | TmLessEqual(fi,TmInt(fi2,num1),t2) ->
      TmLessEqual(fi,TmInt(fi2,num1), eval1 ctx t2)
  | TmLessEqual(fi,t1,t2) ->
      TmLessEqual(fi, eval1 ctx t1, t2)
  | TmTry(fi,TmError(_),t2) ->
      t2
  | TmTry(fi,v1,t2) when isval ctx v1 ->
      v1
  | TmTry(fi,t1,t2) ->
      TmTry(fi,eval1 ctx t1,t2)
  | _ -> 
      raise NoRuleApplies

let rec eval ctx t =
  try let t' = eval1 ctx t
      in eval ctx t'
  with NoRuleApplies -> t

(* ------------------------   SUBTYPING  ------------------------ *)

let evalbinding ctx b = match b with
    TmAbbBind(t,tyT) ->
      let t' = eval ctx t in 
      TmAbbBind(t',tyT)
  | bind -> bind

let istyabb ctx i = 
  match getbinding dummyinfo ctx i with
    TyAbbBind(tyT) -> true
  | _ -> false

let gettyabb ctx i = 
  match getbinding dummyinfo ctx i with
    TyAbbBind(tyT) -> tyT
  | _ -> raise NoRuleApplies

let rec computety ctx tyT = match tyT with
    TyVar(i,_) when istyabb ctx i -> gettyabb ctx i
  | _ -> raise NoRuleApplies

let rec simplifyty ctx tyT =
  try
    let tyT' = computety ctx tyT in
    simplifyty ctx tyT' 
  with NoRuleApplies -> tyT

let rec tyeqv ctx tyS tyT =
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT in
  match (tyS,tyT) with
    (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
       (tyeqv ctx tyS1 tyT1) && (tyeqv ctx tyS2 tyT2)
  | (TyString,TyString) -> true
  | (TyTop,TyTop) -> true
  | (TyBot,TyBot) -> true
  | (TyUnit,TyUnit) -> true
  | (TyId(b1),TyId(b2)) -> b1=b2
  | (TyFloat,TyFloat) -> true
  | (TyVar(i,_), _) when istyabb ctx i ->
      tyeqv ctx (gettyabb ctx i) tyT
  | (_, TyVar(i,_)) when istyabb ctx i ->
      tyeqv ctx tyS (gettyabb ctx i)
  | (TyVar(i,_),TyVar(j,_)) -> i=j
  | (TyBool,TyBool) -> true
  | (TyNat,TyNat) -> true
  | (TyRecord(fields1),TyRecord(fields2)) -> 
       List.length fields1 = List.length fields2
       &&                                         
       List.for_all 
         (fun (li2,tyTi2) ->
            try let (tyTi1) = List.assoc li2 fields1 in
                tyeqv ctx tyTi1 tyTi2
            with Not_found -> false)
         fields2
  | _ -> false

let rec subtype ctx tyS tyT =
   tyeqv ctx tyS tyT ||
   let tyS = simplifyty ctx tyS in
   let tyT = simplifyty ctx tyT in
   match (tyS,tyT) with
     (_,TyTop) -> 
       true
   | (TyBot,_) ->
       true
   | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
       (subtype ctx tyT1 tyS1) && (subtype ctx tyS2 tyT2)
   | (TyRecord(fS), TyRecord(fT)) ->
       List.for_all
         (fun (li,tyTi) -> 
            try let tySi = List.assoc li fS in
                subtype ctx tySi tyTi
            with Not_found -> false)
         fT
   | (TyInt(l1),TyInt(l2)) -> sub_range l2 l1
   | (_,_) -> 
       false

let rec join ctx tyS tyT =
  if subtype ctx tyS tyT then tyT else 
  if subtype ctx tyT tyS then tyS else
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT in
  match (tyS,tyT) with
    (TyRecord(fS), TyRecord(fT)) ->
      let labelsS = List.map (fun (li,_) -> li) fS in
      let labelsT = List.map (fun (li,_) -> li) fT in
      let commonLabels = 
        List.find_all (fun l -> List.mem l labelsT) labelsS in
      let commonFields = 
        List.map (fun li -> 
                    let tySi = List.assoc li fS in
                    let tyTi = List.assoc li fT in
                    (li, join ctx tySi tyTi))
                 commonLabels in
      TyRecord(commonFields)
  | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
      (try TyArr(meet ctx tyS1 tyT1, join ctx tyS2 tyT2)
        with Not_found -> TyTop)
  | (TyInt(l1),TyInt(l2)) -> TyInt(union_range l1 l2)
  | _ -> 
      TyTop

and meet ctx tyS tyT =
  if subtype ctx tyS tyT then tyS else 
  if subtype ctx tyT tyS then tyT else 
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT in
  match (tyS,tyT) with
    (TyRecord(fS), TyRecord(fT)) ->
      let labelsS = List.map (fun (li,_) -> li) fS in
      let labelsT = List.map (fun (li,_) -> li) fT in
      let allLabels = 
        List.append
          labelsS 
          (List.find_all 
            (fun l -> not (List.mem l labelsS)) labelsT) in
      let allFields = 
        List.map (fun li -> 
                    if List.mem li allLabels then
                      let tySi = List.assoc li fS in
                      let tyTi = List.assoc li fT in
                      (li, meet ctx tySi tyTi)
                    else if List.mem li labelsS then
                      (li, List.assoc li fS)
                    else
                      (li, List.assoc li fT))
                 allLabels in
      TyRecord(allFields)
  | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
      TyArr(join ctx tyS1 tyT1, meet ctx tyS2 tyT2)
  | _ -> 
      TyBot

(* ------------------------   TYPING  ------------------------ *)

let rec typeof ctx t =
  match t with
    TmInert(fi,tyT) ->
      tyT
  | TmVar(fi,i,_) -> getTypeFromContext fi ctx i
  | TmAbs(fi,x,tyT1,t2) ->
      let ctx' = addbinding ctx x (VarBind(tyT1)) in
      let tyT2 = typeof ctx' t2 in
      TyArr(tyT1, typeShift (-1) tyT2)
  | TmApp(fi,t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match simplifyty ctx tyT1 with
          TyArr(tyT11,tyT12) ->
            if subtype ctx tyT2 tyT11 then tyT12
            else error fi "parameter type mismatch"
        | TyBot -> TyBot
        | _ -> error fi "arrow type expected")
  | TmTrue(fi) -> 
      TyBool
  | TmFalse(fi) -> 
      TyBool
  | TmIf(fi,t1,t2,t3) ->
      if subtype ctx (typeof ctx t1) TyBool then
        join ctx (typeof ctx t2) (typeof ctx t3)
      else error fi "guard of conditional not a boolean"
  | TmRecord(fi, fields) ->
      let fieldtys = 
        List.map (fun (li,ti) -> (li, typeof ctx ti)) fields in
      TyRecord(fieldtys)
  | TmProj(fi, t1, l) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyRecord(fieldtys) ->
            (try List.assoc l fieldtys
             with Not_found -> error fi ("label "^l^" not found"))
        | _ -> error fi "Expected record type")
  | TmLet(fi,x,t1,t2) ->
     let tyT1 = typeof ctx t1 in
     let ctx' = addbinding ctx x (VarBind(tyT1)) in         
     typeShift (-1) (typeof ctx' t2)
  | TmFix(fi, t1) ->
      let tyT1 = typeof ctx t1 in
      (match simplifyty ctx tyT1 with
           TyArr(tyT11,tyT12) ->
             if subtype ctx tyT12 tyT11 then tyT12
             else error fi "result of body not compatible with domain"
         | _ -> error fi "arrow type expected")
  | TmString _ -> TyString
  | TmUnit(fi) -> TyUnit
  | TmAscribe(fi,t1,tyT) ->
     if subtype ctx (typeof ctx t1) tyT then
       tyT
     else
       error fi "body of as-term does not have the expected type"
  | TmFloat _ -> TyFloat
  | TmTimesfloat(fi,t1,t2) ->
      if subtype ctx (typeof ctx t1) TyFloat
      && subtype ctx (typeof ctx t2) TyFloat then TyFloat
      else error fi "argument of timesfloat is not a number"
  | TmZero(fi) ->
      TyNat
  | TmSucc(fi,t1) ->
      if subtype ctx (typeof ctx t1) TyNat then TyNat
      else error fi "argument of succ is not a number"
  | TmPred(fi,t1) ->
      if subtype ctx (typeof ctx t1) TyNat then TyNat
      else error fi "argument of pred is not a number"
  | TmIsZero(fi,t1) ->
      if subtype ctx (typeof ctx t1) TyNat then TyBool
      else error fi "argument of iszero is not a number"
  | TmInt(fi,num) -> TyInt([(num,num)])
  | TmPlus(fi,t1,t2) -> 
      let ty1 = typeof ctx t1 in
      let ty2 = typeof ctx t2 in
      (match ty1, ty2 with
        TyInt(l1), TyInt(l2) -> 
        let result_range = add_range l1 l2 in
        if sub_range [(0,65535)] result_range then TyInt(result_range)
        else error fi "result overflow"
      | _, _ -> error fi "terms not int")
  | TmMinus(fi,t1,t2) ->
      let ty1 = typeof ctx t1 in
      let ty2 = typeof ctx t2 in
      (match ty1, ty2 with
        TyInt(l1), TyInt(l2) -> TyInt(minus_range l1 l2)
      | _, _ -> error fi "terms not int")
  | TmGreater(fi,t1,t2) | TmGreaterEqual(fi,t1,t2) | TmLess(fi,t1,t2) | TmLessEqual(fi,t1,t2) ->
      let ty1 = typeof ctx t1 in
      let ty2 = typeof ctx t2 in
      (match ty1, ty2 with
        TyInt(_), TyInt(_) -> TyBool
      | _, _ -> error fi "terms not int")
  | TmTry(fi, t1, t2) ->
      join ctx (typeof ctx t1) (typeof ctx t2)
  | TmError(fi) ->
      TyBot
  | TmCast(fi, t1, rl) ->
      let ty1 = typeof ctx t1 in
      (match ty1 with TyInt(_) -> TyInt(rl)
                    | _ -> error fi "terms not int")
