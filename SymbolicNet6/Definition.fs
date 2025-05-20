namespace MathNet.Symbolics

open MathNet.Numerics.LinearAlgebra
open System.Collections.Concurrent
module Definition =
    type Cur = decimal //==> evaluate 用 dict 送進去的

    type DefOutput =
    | OutVar of Symbol list //輸出 Expression list 最後一個 Expression 中的變數，不存在則從 ScopedContext 取，最終包成 NestedExpr
    | OutFP //輸出最後一個 Expression evaluate 的 FloatingPoint
    | OutCtx //輸出 FloatingPoint.Context

    type GlobalContext = ConcurrentDictionary<string, FloatingPoint>
    type ScopedContext = ConcurrentDictionary<string, FloatingPoint>

    type AlmightFun =
        GlobalContext (* 頂層 evaluate2 會共用 GlobalContext *) -> ScopedContext (* 前一輸出之 context，單一 DTProc 連續多個 DefBody 會共用 ScopedContext *) -> FloatingPoint option (*
        前次輸出(第0層為 None)
        --> [錯誤描述] 用來支援 NestedExpr，
        --> [錯誤描述] NestedExpr 的每一個 Expression 都是獨立執行的，
        --> [錯誤描述] 單一一個 NestedExpr 表一個 scope ，
        --> [錯誤描述] FloatingPoint list 的最後一個則必須符合輸出能夠讓下一次輸入吃進去，
        --> [錯誤描述] 也就是 (Symbol list) * DefBody 當中 (p, _, _) 的 p
        --> [錯誤描述] 系統變數則是用於確保 Evalute 須提供特定 系統資料 (如果 evalutate 中沒有輸入則要報錯，上層輸出沒輸出也要報錯)
        *) -> (* ScopedContext 本次輸出 context -> //因為 ctx 應該是在Proc 範圍內持續存在，故改為不輸出 *) FloatingPoint

    type DefBody =
    | DBExp of Expression list * DefOutput //獨立執行，整個 list 是獨立 ScopedContext，但是 (_, DefOutput) 最後的 OutVar (s list) 是輸出的 scope 內的變數，不存在則從 scope context 取，最末一輸出必須符合下一層 (Symbol list) * DefBody 當中 (p, _) 的 p
                                         //OutCTX 用以表示輸出 Context (按 key 輸入) or NestedExpr (按順序輸入)
                                         //記得，Evaluate 最終全部都是要輸出 FloatingPoint 的
    | DBFun of AlmightFun //對於一般的 DefType 來說，輸出都是單一 FloatingPoint，這邊簽名吃 FloatingPoint list 主要是先判斷 NestedExpr 如果是就吃 list 不是就吃單一 FloatingPoint，這樣寫會方便些，
                          //輸出是 FloatingPoint list 對於多引數函數方便些，例如 vec(almightFun(xxx))，如果almightFun輸出4位則vec吃到4位
                          //此邏輯在 evaluate2 中支援
                          //另外，global context 於首次 evaluate 時初始化後由 evaluate2 提供

    type DefType =
    | DTExp of (Symbol list) * Expression //用表達式表示函數 body，symbol 是表達式中參數名
    | DTProc of ((Symbol list) * DefBody) list //用表達式/F#函數表示函數 body，symbol 是表達式中參數名，系統變數(例如當根位置, context 等等)由 Evaluate 提供
    | DTFunAction of (unit -> unit)
    | DTFunI1toI1 of (int -> int)
    | DTFunF2toV1 of (float -> float -> Vector<float>)
    | DTCurF2toV1 of (Cur -> float -> float -> Vector<float>) * Symbol
    | DTCurF3toV1 of (Cur -> float -> float -> float -> Vector<float>) * Symbol // cur 以 decimal 表示當根位置，然後傳入的參數是 float * float * float
    | KeyWord

    let mutable funDict = new System.Collections.Concurrent.ConcurrentDictionary<string, DefType>()

    let kwlist = [ "vec", true; "mat_by_row", true; "mat_by_col", true; "mat_multiply", true;
                   "htensor", true; 
                   "gtensor", true;
                   "list_of", true; "lo", true;
                   //"htensor", true
                   "str"    , true
                   ]

    let keyWord = dict kwlist

    kwlist |> List.iter (fun (k, _) -> funDict.TryAdd(k, KeyWord) |> ignore)

    let defineSafe fnm exp =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.TryAdd (fnm, DTExp exp)

    let define fnm exp =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.AddOrUpdate(
            fnm
            , (fun nm -> DTExp exp)
            , (fun nm cur_exp -> DTExp exp)
        )

    let defProc fnm l =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.AddOrUpdate(
            fnm
            , (fun nm -> DTProc l)
            , (fun nm cur_exp -> DTProc l)
        )


    let defAct fnm f =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.AddOrUpdate(
            fnm
            , (fun nm -> DTFunAction f)
            , (fun nm cur_exp -> DTFunAction f)
        )

    let def1ito1i fnm f =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.AddOrUpdate(
            fnm
            , (fun nm -> DTFunI1toI1 f)
            , (fun nm cur_exp -> DTFunI1toI1 f)
        )


    let def2fto1v fnm f =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.AddOrUpdate(
            fnm
            , (fun nm -> DTFunF2toV1 f)
            , (fun nm cur_exp -> DTFunF2toV1 f)
        )

    let cur2fto1v fnm f =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.AddOrUpdate(
            fnm
            , (fun nm -> DTCurF2toV1 f)
            , (fun nm cur_exp -> DTCurF2toV1 f)
        )

    let cur3fto1v fnm f =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.AddOrUpdate(
            fnm
            , (fun nm -> DTCurF3toV1 f)
            , (fun nm cur_exp -> DTCurF3toV1 f)
        )
