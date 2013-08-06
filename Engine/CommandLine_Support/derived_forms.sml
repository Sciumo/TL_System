
(* =========================================================================================================================== *)
structure DerivedForms = struct
open CONCRETE_REPRESENTATION

val DEBUG = false;


val LM     = "\n";
val INDENT = "   ";

fun printTree LM (tree( t_node(name, x_info), tree_list ) ) = let 
                                                                  val new_LM = LM ^ INDENT
                                                              in 
                                                                  print(LM ^ name ); 
                                                                        
                                                                  map (printTree new_LM) tree_list;
                                                                  ()
                                                              end
  | printTree LM (tree( schema_var(name, x_info), _ ) ) = let 
                                                              val new_LM = LM ^ INDENT
                                                           in 
                                                              print(LM ^ name )
                                                           end
                                                                                                                                                    
  | printTree LM t = raise General.Fail("Error in derived_forms.printTree");
                                                    

(* =========================================================================================================================== *)  
fun splitList( x :: xs ) = (x,xs)
  | splitList _ = raise General.Fail("Error in derived_forms.splitList.\n")

(* --------------------------------------------------------------------------------------------------------------------------- *)
fun getList( tree(t_node("qualified_id_list",_), 
                        [
                            qualified_id,
                            qualified_id_list
                        ]
                  )
            )
            = qualified_id :: getList qualified_id_list
  | getList( tree(t_node("qualified_id_list",_), [tree(t_node("",_),[])]) )  = []

(* --------------------------------------------------------------------------------------------------------------------------- *)          
fun getLeaf( tree( t_node(x,_), []  ) ) = x
  | getLeaf( tree( _          , xs ) )  = foldr (op ^) "" (map getLeaf xs)
  
(* --------------------------------------------------------------------------------------------------------------------------- *)            
fun createEmptyImportDefList( info1 ) =  tree(t_node("importDef_list",info1), [tree(t_node("",info1),[])])        
  
(* --------------------------------------------------------------------------------------------------------------------------- *)              
fun getInfo (tree(t_node(_,info1), _ )) = info1  

(* --------------------------------------------------------------------------------------------------------------------------- *)              
fun createExprFromQualifiedId qualifiedId info1 = 
    tree( t_node("expr",info1),
                [
                    tree(t_node("application",info1),
                                [
                                    tree(t_node("base",info1),
                                                [
                                                    tree(t_node("primitive",info1),
                                                                [
                                                                    qualifiedId
                                                                ]
                                                        )
                                                ]
                                        )
                                ]
                        )
                ]
        )


(* --------------------------------------------------------------------------------------------------------------------------- *)                                                      
fun encloseExprInParensAndCovertToBase( expr as tree(t_node("expr",info1), _ ) ) = 
    tree(t_node("base",info1),
                [
                    tree(t_node("(",info1),[]),
                    expr,
                    tree(t_node(")",info1),[])
                ]
        )
              
(* =========================================================================================================================== *)                
(* (r1 <; r2 <; r3).process => (r1.process <; r2.process <; r3.process) *)
fun distributeDotAccess id 
                        dot 
                        ( t as tree(t_node("qualified_id",info1),
                                    [
                                        tree(t_node("id",info2), children)
                                    ]
                                  )
                        ) = 
                          tree(t_node("qualified_id",info1),
                                [
                                    t,
                                    dot,
                                    id
                                ]
                             )
  | distributeDotAccess id dot (tree(x,xs)) = tree(x, map (distributeDotAccess id dot) xs)
                       
                       
(* --------------------------------------------------------------------------------------------------------------------------- *)                                                      
fun unfold  IdStr
            derivedStrategy
            (
                t1 as tree(t_node("base",_),
                                [
                                    tree(t_node("primitive",_),
                                                [
                                                    tree(t_node("qualified_id",_), 
                                                            [
                                                                id,
                                                                dot,
                                                                tree(t_node("qualified_id",_),
                                                                            [
                                                                                tId as tree(t_node("id",_), _)
                                                                            ]
                                                                     )
                                                            ]
                                                        )
                                                ]
                                        )
                                ]
                          )
            )
            = if getLeaf id = IdStr then 
                let
                    val instantiatedStrategy = distributeDotAccess tId dot derivedStrategy 
                in
                    if DEBUG then
                        (
                            print("\n\n==============================");
                            print("\nInstantiated Strategy");
                            print("\n==============================\n\n");
                            print("tId = " ^ getLeaf tId ^ "\n\n");
                            printTree LM instantiatedStrategy;
                            print("\n==============================\n\n")
                        )
                    else ();
                    
                    instantiatedStrategy
                end
              else t1
    
  | unfold _ _ (t as tree(t_node("target_tree_phrase", _), _)) = t
  | unfold IdStr derivedStrategy (tree(x,xs)) = tree(x, map (unfold IdStr derivedStrategy) xs)
    
(* =========================================================================================================================== *)  
fun deconstruct(tree(t_node("derivedForm_list",_), [tree(t_node("",_),[])])) = NONE
  | deconstruct(tree(t_node("derivedForm_list",_),
                        [
                            tree(t_node("derivedForm",_), 
                                        [
                                            tree(t_node("ModuleSet",_),
                                                        [
                                                            derivedFormKeyword,
                                                            Id,
                                                            eqKeyword,
                                                            binaryCombinator,
                                                            curlyLeft,
                                                            qualifiedIdList,
                                                            curlyRight
                                                        ]
                                                )
                                        ]
                                )
                            ,
                            tree(t_node("derivedForm_list",_), [tree(t_node("",_),[])])
                        ]
                     )
                )
                =
                SOME(
                        Id,
                        binaryCombinator,
                        getList qualifiedIdList
                    )
  | deconstruct _  = raise General.Fail("Error in DerivedForms.deconstruct\n")             
  
(* =========================================================================================================================== *)    
fun createImportList(importMode, qualifiedId :: rest, importDef_list ) =
    let 
        fun add(importDef_list as tree(t_node("importDef_list",info1), children )) =

                tree(t_node("importDef_list",info1), 
                                [
                                    tree(t_node("importDef",info1),
                                            [
                                                importMode,
                                                qualifiedId
                                            ] 
                                      )
                                 ,
                                 importDef_list
                                ]
                    ) 
       
        val term = add importDef_list
    in
        createImportList(importMode, rest, term)
    end
  | createImportList(_,[], import_list) = import_list
      
               
(* =========================================================================================================================== *)    
fun processImportData(IdStr, importDef_list) =
    let
        (* ------------------------------------------------------------------------------------------------------------------ *)
        fun combine( SOME( importMode, info1 ), newImportDef_list ) = SOME(importMode, info1, newImportDef_list) 
          | combine( NONE, _ ) = NONE
        
        (* ------------------------------------------------------------------------------------------------------------------ *)        
        fun extractImportData(IdStr,
                              tree(t_node("importDef_list",info1), 
                                         [
                                            tree(t_node("importDef",info2),
                                                       [
                                                         importMode,
                                                         qualifiedId
                                                       ] 
                                                )
                                            ,
                                            importDef_list
                                          ]
                                  )
                              ) = if getLeaf qualifiedId = IdStr 
                                  then SOME( importMode, info2 )
                                  else extractImportData( IdStr, importDef_list )
          | extractImportData _ = NONE 
              
        (* ------------------------------------------------------------------------------------------------------------------ *)
        fun deleteDerivedImport(IdStr,
                                tree(t_node("importDef_list",info1), 
                                           [
                                              tree(t_node("importDef",info2),
                                                         [
                                                           importMode,
                                                           qualifiedId
                                                         ] 
                                                  )
                                               ,
                                              importDef_list
                                            ]
                                    )
                                ) = if getLeaf qualifiedId = IdStr 
                                    then importDef_list
                                    else tree(t_node("importDef_list",info1), 
                                                       [
                                                          tree(t_node("importDef",info2),
                                                                     [
                                                                       importMode,
                                                                       qualifiedId
                                                                     ] 
                                                              )
                                                           ,
                                                          deleteDerivedImport(IdStr,importDef_list)
                                                        ]
                                             )

          | deleteDerivedImport(_, emptyTree ) =  emptyTree

        (* ------------------------------------------------------------------------------------------------------------------ *)
       
        val importDataOpt     = extractImportData(IdStr, importDef_list)
        val newImportDef_list = deleteDerivedImport(IdStr, importDef_list)
    in
        combine( importDataOpt, newImportDef_list )
    end
 
(* =========================================================================================================================== *)    
fun combineImportLists(derivedImportList,
                       tree(t_node("importDef_list",info1), 
                                   [
                                      tree(t_node("importDef",info2),
                                                 [
                                                   importMode,
                                                   qualifiedId
                                                 ] 
                                          )
                                       ,
                                      importDef_list
                                    ]
                            )
                      ) = tree(t_node("importDef_list",info1), 
                                   [
                                      tree(t_node("importDef",info2),
                                                 [
                                                   importMode,
                                                   qualifiedId
                                                 ] 
                                          )
                                       ,
                                      combineImportLists(derivedImportList,importDef_list)
                                    ]
                            )
                            
  | combineImportLists(derivedImportList,
                       tree(t_node("importDef_list",_), [tree(t_node("",_),[])])  
                      ) 
                      = derivedImportList

(* =========================================================================================================================== *)                         
fun createStrategy(binaryCombinatorStr, qualifiedIdList) = 
    let
        fun combineExprIntoStrategy binaryCombinatorStr s expr info1 =
            tree(t_node("expr",info1),
                        [
                            s,
                            tree(t_node(binaryCombinatorStr,info1), []),
                            expr
                        ]
                )
                
        fun aux(qualifiedId :: rest, strategyAcc) =
            let
                val info1     = getInfo qualifiedId
                val qIdAsExpr = createExprFromQualifiedId qualifiedId info1
                val strategy  = combineExprIntoStrategy binaryCombinatorStr strategyAcc qIdAsExpr info1 
            in
                aux(rest,strategy)
            end

          | aux([], strategyAcc) = encloseExprInParensAndCovertToBase strategyAcc
          
        val (qualifiedId,rest) = splitList (List.rev qualifiedIdList)
        val strategyAcc        = createExprFromQualifiedId qualifiedId (getInfo qualifiedId)  
        
        val strategy           = aux( rest, strategyAcc )
    in
        if DEBUG then printTree LM strategy else ();
        
        strategy
    end
(* =========================================================================================================================== *)   
fun process    derivedForm_list import_list decl_list = 
    let
        fun derivedUsedInImport(SOME(importMode, info1, ImportDefListWithoutDerivedImport), qualifiedIdList) = 
                let
                    val _ = if DEBUG then print("\n****Derived form id occurs in import list.\n") else ()
                    
                    val emptyImportDef_list = createEmptyImportDefList info1 
                    val derivedImportList   = createImportList (importMode, qualifiedIdList, emptyImportDef_list)
                    val processedImportList = combineImportLists(derivedImportList, ImportDefListWithoutDerivedImport)
                in
                   if DEBUG then printTree LM processedImportList else ();

                    processedImportList                   
                end
          | derivedUsedInImport _ = import_list      
                
                
        fun derivedExists NONE = (import_list,decl_list)
          | derivedExists (SOME (Id,binaryCombinator,qualifiedIdTermList)) =
                let      
                    val _ = if DEBUG then print("\n****Derived form exists involving: " ^ getLeaf Id ^ "\n") else ()
                    
                    val IdStr           = getLeaf Id
                    val importDataOpt   = processImportData(IdStr, import_list)
                    val newImportList   = derivedUsedInImport(importDataOpt, qualifiedIdTermList) 
                                       
                    val derivedStrategy = createStrategy(getLeaf binaryCombinator, qualifiedIdTermList) 
                    val newDeclList     = unfold IdStr derivedStrategy decl_list
                in
                
                    if DEBUG then 
                        (
                            print("\n\nImport list is: \n");
                            printTree LM newImportList;
                            
                            print("\n\nDecl list is: \n");
                            printTree LM newDeclList;
                            print("\n\n")
                        )
                    else ();
                        
                    (newImportList,newDeclList)
                end
        
        val deconstructedOpt  = deconstruct derivedForm_list
    in
        derivedExists deconstructedOpt
    end
(* --------------------------------------------------------------------------------------------------------------------------- *)            
  |    process _ _ _ = raise General.Fail("Error in DerivedForms.process\n")

  
(* =========================================================================================================================== *)  
end; (* struct *)
(* =========================================================================================================================== *)
