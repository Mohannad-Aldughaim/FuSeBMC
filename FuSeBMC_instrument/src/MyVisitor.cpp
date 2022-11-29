#include <clang/AST/RecursiveASTVisitor.h>
#include <clang/Basic/SourceManager.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/Stmt.h>
#include <clang/AST/StmtCXX.h>
#include <clang/AST/Expr.h>
#include <clang/AST/ExprCXX.h>
#include <clang/AST/Decl.h>
#include <clang/Rewrite/Core/Rewriter.h>
#include <clang/Rewrite/Frontend/Rewriters.h>
#include <clang/Basic/SourceManager.h>
#include <clang/AST/ASTConsumer.h>
#include <clang/Basic/FileManager.h>
#include <clang/Basic/SourceManager.h>
#include <clang/Basic/TargetInfo.h>
#include <clang/Basic/TargetOptions.h>
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Lex/Preprocessor.h>
#include <clang/Parse/ParseAST.h>
#include <clang/Rewrite/Core/Rewriter.h>
#include <clang/Rewrite/Frontend/Rewriters.h>
#include <llvm/Support/Host.h>
#include <llvm/Support/raw_ostream.h>
#include <clang/Lex/Token.h>
#include <clang/AST/ParentMap.h>
#include <map>
#include <cstdio>
#include <memory>
#include <sstream>
#include <string>
#include <iostream>

#include <MyHolder.h>
#include <MyVisitor.h>
#include <GoalCounter.h>
#include <MyOptions.h>
#include <FuSeBMC_instrument.h>

#include "FuncDeclInfo.h"


using namespace clang;
extern MyOptions *myOptions;
extern FuncDeclList *funcDeclList;
extern unsigned mainFileID;
GoalCounter &goalCounter = GoalCounter::getInstance();
int infinteWhileNum = 0;

MyVisitor::MyVisitor(Rewriter &R, MyHolder &H, Rewriter &rewriter, std::map<int, goto_contractort *> *contractors_map)
        : TheRewriter(R), TheHolder(H), interval_rewriter(rewriter), contractor_map(contractors_map) {
    this->sourceManager = TheHolder.SourceManager;
    this->aSTContext = TheHolder.ASTContext;
    c = new goto_contractort();
}

bool MyVisitor::TraverseDecl(Decl *decl) {

    return Base::TraverseDecl(decl);
}

tok::TokenKind MyVisitor::getTokenKindInLocation(SourceLocation location) {
    Token tmpToken;
    SourceLocation beginningOfToken = Lexer::GetBeginningOfToken(location, *this->sourceManager,
                                                                 this->aSTContext->getLangOpts());
    const bool invalid = Lexer::getRawToken(beginningOfToken, tmpToken, *this->sourceManager,
                                            this->aSTContext->getLangOpts());
    //assert(!invalid && "Expected a valid token.");
    if (invalid)
        return tok::NUM_TOKENS;
    return tmpToken.getKind();
}

bool MyVisitor::checkStmt(Stmt *S, SourceLocation initialLoc, SourceLocation endLocHint,
                          InstrumentOption instrumentOption, bool isIfIfOrElseIf) {
    // 1) If there's a corresponding "else" or "while", the check inserts "} "
    // right before that token.
    // 2) If there's a multi-line block comment starting on the same line after
    // the location we're inserting the closing brace at, or there's a non-comment
    // token, the check inserts "\n}" right before that token.
    // 3) Otherwise the check finds the end of line (possibly after some block or
    // line comments) and inserts "\n}" right before that EOL.
    if (!S) return false;
    //llvm::outs()<< "SSSSSSSSSSSSSS\r\n" << S->getStmtClassName() ;
    //S->dumpColor();
    const SourceManager &sourceManager = *TheHolder.SourceManager;
    ASTContext *astContext = TheHolder.ASTContext;
    // Already inside braces.
    if (isa<CompoundStmt>(S)) {
        //while(x){compound_statement} ; if(x){compound_statement}
        CompoundStmt *compoundStmt = cast<CompoundStmt>(S);
        if (myOptions->addLabels) {
            GoalType tmpGoalType = GoalType::COMPOUND;
            if (instrumentOption == InstrumentOption::MUST_INSERT_ELSE ||
                instrumentOption == InstrumentOption::STMT_IS_IF)
                tmpGoalType = GoalType::IF;
            else if (instrumentOption == InstrumentOption::STMT_IS_ELSE)
                tmpGoalType = GoalType::ELSE;
            else if (instrumentOption == InstrumentOption::PARENT_IS_FOR)
                tmpGoalType = GoalType::FOR;
            else if (instrumentOption == InstrumentOption::PARENT_IS_CXX_FOR_RANGE)
                tmpGoalType = GoalType::CXX_FOR_RANGE;
            else if (instrumentOption == InstrumentOption::PARENT_IS_DO_WHILE)
                tmpGoalType = GoalType::DO_WHILE;
            else if (instrumentOption == InstrumentOption::PARENT_IS_WHILE)
                tmpGoalType = GoalType::WHILE;
            TheRewriter.InsertTextAfter(compoundStmt->getLBracLoc().getLocWithOffset(1),
                                        (isIfIfOrElseIf ? "" : GET_LINE() +
                                                               goalCounter.GetNewGoalForFuncDecl(current_func,
                                                                                                 tmpGoalType) +
                                                               GET_LINE_E()));
            if (tmpGoalType == GoalType::IF) {
                if (!isIfIfOrElseIf) {
                    if(c->map.size() !=0) {
                        (*contractor_map)[goalCounter.counter] = c;
                        interval_rewriter.InsertTextAfter(compoundStmt->getLBracLoc().getLocWithOffset(1),
                                                          (GET_LINE() +
                                                           "Frama_C_show_each_GOAL_" +
                                                           to_string(goalCounter.counter) + "_" +
                                                           to_string(
                                                                   (*contractor_map)[goalCounter.counter]->map.size()) +
                                                           "_(" +
                                                           (*contractor_map)[goalCounter.counter]->get_list_of_vars() +
                                                           ");" +
                                                           GET_LINE_E()));
                    }
                    c = new goto_contractort();
                }
            }
        }
        if (instrumentOption == InstrumentOption::MUST_INSERT_ELSE && myOptions->addElse)
            TheRewriter.InsertTextBefore(compoundStmt->getRBracLoc().getLocWithOffset(1),
                                         GET_LINE() + "\nelse\n{" +
                                         goalCounter.GetNewGoalForFuncDecl(current_func, GoalType::EMPTY_ELSE) +
                                         "}" + GET_LINE_E());

        bool is_for_CxxFor_while = (instrumentOption == InstrumentOption::PARENT_IS_FOR ||
                                    instrumentOption == InstrumentOption::PARENT_IS_CXX_FOR_RANGE ||
                                    instrumentOption == InstrumentOption::PARENT_IS_WHILE //||
                //instrumentOption == InstrumentOption::PARENT_IS_DO_WHILE
        );

        //TODO: handle label after Loop When instrumentOption == InstrumentOption::PARENT_IS_DO_WHILE .


        //if(instrumentOption == InstrumentOption::PARENT_IS_LOOP && myOptions->addLabelAfterLoop)
        if (is_for_CxxFor_while && myOptions->addLabelAfterLoop)
            TheRewriter.InsertTextBefore(compoundStmt->getRBracLoc().getLocWithOffset(1),
                                         GET_LINE() +
                                         goalCounter.GetNewGoalForFuncDecl(current_func, GoalType::AFTER_LOOP) +
                                         GET_LINE_E());
        return false;
    }// END If Compound

    // Treat macros.
    CharSourceRange fileRange = Lexer::makeFileCharRange(CharSourceRange::getTokenRange(S->getSourceRange()),
                                                         sourceManager, astContext->getLangOpts());
    if (fileRange.isInvalid())
        return false;
#ifdef MYDEBUG
    // InitialLoc points at the last token before opening brace to be inserted.
    assert(initialLoc.isValid());
#endif
    // Convert InitialLoc to file location, if it's on the same macro expansion
    // level as the start of the statement. We also need file locations for
    // Lexer::getLocForEndOfToken working properly.
    initialLoc = Lexer::makeFileCharRange(
            CharSourceRange::getCharRange(initialLoc, S->getBeginLoc()),
            sourceManager, astContext->getLangOpts()).getBegin();
    if (initialLoc.isInvalid())
        return false;
    SourceLocation startLoc = Lexer::getLocForEndOfToken(initialLoc, 0, sourceManager, astContext->getLangOpts());

    // StartLoc points at the location of the opening brace to be inserted.
    SourceLocation endLoc;
    std::string closing;
    if (endLocHint.isValid()) {
        endLoc = endLocHint;
        closing = "\n" + D("/*A*/") + "}\n";
        //TheRewriter.InsertTextAfter(endLoc,closing);
    } else {
        const auto fileRangeEndLoc = fileRange.getEnd().getLocWithOffset(-1);
        endLoc = findEndLocation(fileRangeEndLoc);
        closing = "\n" + D("/*B*/") + "}\n";
        //TheRewriter.InsertTextAfter(endLoc,closing);
    }
#ifdef MYDEBUG
    assert(startLoc.isValid());
    assert(endLoc.isValid());
#endif
    bool isif = false;
    if (myOptions->addLabels) {
        GoalType tmpGoalType = GoalType::COMPOUND;

        if (instrumentOption == InstrumentOption::MUST_INSERT_ELSE ||
            instrumentOption == InstrumentOption::STMT_IS_IF)
            tmpGoalType = GoalType::IF;
        else if (instrumentOption == InstrumentOption::STMT_IS_ELSE)
            tmpGoalType = GoalType::ELSE;

        else if (instrumentOption == InstrumentOption::PARENT_IS_FOR)
            tmpGoalType = GoalType::FOR;
        else if (instrumentOption == InstrumentOption::PARENT_IS_CXX_FOR_RANGE)
            tmpGoalType = GoalType::CXX_FOR_RANGE;
        else if (instrumentOption == InstrumentOption::PARENT_IS_DO_WHILE)
            tmpGoalType = GoalType::DO_WHILE;
        else if (instrumentOption == InstrumentOption::PARENT_IS_WHILE)
            tmpGoalType = GoalType::WHILE;

        TheRewriter.InsertTextAfter(startLoc, GET_LINE() + "\n{\n" +
                                              ((isIfIfOrElseIf ? "" : goalCounter.GetNewGoalForFuncDecl(current_func,
                                                                                                        tmpGoalType))) +
                                              GET_LINE_E());

        if (tmpGoalType == GoalType::IF) {
            if (!isIfIfOrElseIf) {
                if(c->map.size() !=0) {
                    (*contractor_map)[goalCounter.counter] = c;
                    interval_rewriter.InsertTextAfter(startLoc, GET_LINE() + "\n{\n" +
                                                                (GET_LINE() +
                                                                 "Frama_C_show_each_GOAL_" +
                                                                 to_string(goalCounter.counter) +
                                                                 "_" +
                                                                 to_string(
                                                                         (*contractor_map)[goalCounter.counter]->map.size()) +
                                                                 "_(" +
                                                                 (*contractor_map)[goalCounter.counter]->get_list_of_vars() +
                                                                 ");" +
                                                                 GET_LINE_E()));
                }
                c = new goto_contractort();
                isif = true;
            }
        }
    }
    if (instrumentOption == InstrumentOption::MUST_INSERT_ELSE && myOptions->addElse) {
        TheRewriter.InsertTextBefore(endLoc, GET_LINE() + closing + "else \n{" +
                                             goalCounter.GetNewGoalForFuncDecl(current_func, GoalType::EMPTY_ELSE) +
                                             "}" + GET_LINE_E());
    } else {
#ifdef MYDEBUG
        //std::cout << "LINE:"<< endLoc.printToString(sourceManager) << " V_counter:" << V_counter << std::endl;
#endif
        if (myOptions->addLabels) {
            bool is_for_CxxFor_while = (instrumentOption == InstrumentOption::PARENT_IS_FOR ||
                                        instrumentOption == InstrumentOption::PARENT_IS_CXX_FOR_RANGE ||
                                        instrumentOption == InstrumentOption::PARENT_IS_WHILE //||
                    //instrumentOption == InstrumentOption::PARENT_IS_DO_WHILE
            );

            //TODO: handle label after Loop When instrumentOption == InstrumentOption::PARENT_IS_DO_WHILE
            //if(instrumentOption == InstrumentOption::PARENT_IS_LOOP && myOptions->addLabelAfterLoop)
            if (is_for_CxxFor_while && myOptions->addLabelAfterLoop)
                closing += D("/*C*/") + goalCounter.GetNewGoalForFuncDecl(current_func, GoalType::AFTER_LOOP);
            TheRewriter.InsertTextBefore(endLoc, GET_LINE() + closing + GET_LINE_E());
            //if(tmpGoalType == GoalType::IF)
            if (isif) { interval_rewriter.InsertTextBefore(endLoc, GET_LINE() + closing + GET_LINE_E()); }
        }
    }
    return true;
}

bool MyVisitor::containNonDetCall(Stmt *S) {
    if (isa<CallExpr>(S)) {
        //std::cout << "IT IS CallExpr !!" << std::endl;
        CallExpr *call = cast<CallExpr>(S);
        if (!call) {
            std::cout << "It is not a call.... " << std::endl;
            return false;
        }
        FunctionDecl *func_decl = call->getDirectCallee();
        if (!func_decl) {
            return false;
        }
        IdentifierInfo *identifierInfo = func_decl->getIdentifier();
        if (!identifierInfo) {
            return false;
        }
        //unsigned StartLine = SM.getSpellingLineNumber(call->getLocStart());
        //std::cout << "StartLine=" << StartLine << std::endl;
        llvm::StringRef funcName = identifierInfo->getName();
        //string funcNameStr = funcName.str();
        if (funcName.startswith("__VERIFIER_nondet_")) {
            return true;


#if MYDEBUG
            //std::cout << "NonDetCall in startLine=" << startLine << std::endl;
#endif
        }
        //if (identifierInfo->getName()=="reach_error")
        //	TheRewriter.ReplaceText(call->getBeginLoc(), identifierInfo->getName().size(), " reach_original_error");
    }
    for (Stmt::child_iterator i = S->child_begin(), e = S->child_end(); i != e; ++i) {
        Stmt *child = *i;
        if (!child) continue;
        if (isa<NullStmt>(child)) continue;
        if (containNonDetCall(child))
            return true;
    }
    return false;
}

void MyVisitor::check(Stmt *S) {

    // Get location of closing parenthesis or 'do' to insert opening brace.
    if (isa<ForStmt>(S)) {
        ForStmt *forStmt = cast<ForStmt>(S);
        checkStmt(forStmt->getBody(), forStmt->getRParenLoc(), SourceLocation(), InstrumentOption::PARENT_IS_FOR,
                  false);
    } else if (isa<CXXForRangeStmt>(S)) {
        CXXForRangeStmt *cXXForRangeStmt = cast<CXXForRangeStmt>(S);
        checkStmt(cXXForRangeStmt->getBody(), cXXForRangeStmt->getRParenLoc(), SourceLocation(),
                  InstrumentOption::PARENT_IS_CXX_FOR_RANGE, false);
    } else if (isa<DoStmt>(S)) {
        /**do {} while(x);*/
        DoStmt *doStmt = cast<DoStmt>(S);
        if (myOptions->addLabelAfterLoop) {
            SourceLocation locSemi = skipCommentAndWhitespaceUntilSemi(doStmt->getWhileLoc());
            if (locSemi.isValid())
                TheRewriter.InsertTextBefore(locSemi.getLocWithOffset(1), GET_LINE() +
                                                                          goalCounter.GetNewGoalForFuncDecl(
                                                                                  current_func, GoalType::AFTER_LOOP) +
                                                                          GET_LINE_E());
        }
        checkStmt(doStmt->getBody(), doStmt->getDoLoc(), doStmt->getWhileLoc(), InstrumentOption::PARENT_IS_DO_WHILE,
                  false);
    } else if (isa<WhileStmt>(S)) {
        WhileStmt *whileStmt = cast<WhileStmt>(S);
        SourceLocation startLoc = findRParenLocInIfOrWhile(whileStmt);
        if (startLoc.isInvalid())
            return;
        if (myOptions->handleInfiniteWhileLoop && infinteWhileNum == 0)
            handleInfiniteWhileLoop(whileStmt, startLoc);
        //TheRewriter.InsertTextBefore(whileStmt->getRParenLoc(),"/*B*/");
        checkStmt(whileStmt->getBody(), startLoc, SourceLocation(), InstrumentOption::PARENT_IS_WHILE, false);
    } else if (isa<IfStmt>(S)) {
        IfStmt *ifStmt = cast<IfStmt>(S);
        SourceLocation startLoc = findRParenLocInIfOrWhile(ifStmt);
        if (startLoc.isInvalid())
            return;

        c->get_contractors(ifStmt->getCond());

        Stmt *Else = ifStmt->getElse();
        Stmt *Then = ifStmt->getThen();
        bool isIfIf = isa<IfStmt>(Then) || isCompoundWithOneIf(Then);
        //if(Else && !isa<IfStmt>(Else))
        if (Else) {
            // We must check here (can without Else)
            bool isElseIf = isa<IfStmt>(Else) || isCompoundWithOneIf(Else);
            // Omit 'else if' statements here, they will be handled directly.
            checkStmt(Then, startLoc, ifStmt->getElseLoc(), InstrumentOption::STMT_IS_IF, isIfIf);
            checkStmt(Else, ifStmt->getElseLoc(), SourceLocation(), InstrumentOption::STMT_IS_ELSE, isElseIf);
        } else {
            checkStmt(Then, startLoc, ifStmt->getElseLoc(), InstrumentOption::MUST_INSERT_ELSE, isIfIf);
        }
    } else if (isa<SwitchStmt>(S)) {
        //llvm::outs()<<  current_func->getNameAsString() << "\n";
        SwitchStmt *switchStmt = cast<SwitchStmt>(S);
        const SwitchCase *switchCase = switchStmt->getSwitchCaseList();
        while (switchCase != nullptr) {
            if (myOptions->addLabels)
                TheRewriter.InsertTextAfter(switchCase->getColonLoc().getLocWithOffset(1),
                                            goalCounter.GetNewGoalForFuncDecl(current_func, GoalType::IF));
            switchCase = switchCase->getNextSwitchCase();
        }
        //llvm::outs()<< "\nXXXXXXXXXX\r\n" << S->getStmtClassName() ;
        //S->dumpColor();
    } else if (isa<ReturnStmt>(S)) {
        if (myOptions->handleReturnInMain && this->current_func != NULL &&
            this->current_func->getNameAsString() == "main") {
            ReturnStmt *returnStmt = cast<ReturnStmt>(S);
            //returnStmt-> getRetValue()->dumpColor();
            //llvm::outs() << "ret_b:" << returnStmt->getBeginLoc().getRawEncoding() << "\n";
            //llvm::outs() << "ret_e:" << returnStmt->getEndLoc().getRawEncoding() << "\n";
            //TheRewriter.InsertTextAfter(returnStmt->getBeginLoc().getLocWithOffset(0) ,GET_LINE() +  D("/*ret_B*/") + GET_LINE_E());
            clang::Expr *expr = returnStmt->getRetValue();
            if (expr) {
                //TheRewriter.InsertTextAfter(expr->getBeginLoc() ,GET_LINE() +  "/*exp_b*/" + "" + GET_LINE_E());
                //TheRewriter.InsertTextAfter(expr->getEndLoc() ,GET_LINE() +  "/*exp_e*/" + "" + GET_LINE_E());
                SourceLocation expr_b = expr->getBeginLoc();
                bool isSemiFound = false;
                Token tmpToken;
                while (true) {
                    while (isWhitespace(*FullSourceLoc(expr_b, *this->sourceManager).getCharacterData()))
                        expr_b = expr_b.getLocWithOffset(1);
                    const bool invalid = Lexer::getRawToken(expr_b, tmpToken, *this->sourceManager,
                                                            this->aSTContext->getLangOpts());
                    //llvm::outs() << "expr_e_raw_loc:" << expr_b.getRawEncoding() << "\n";
                    //llvm::outs() << "NAME:(" << tmpToken.getName() << ")\n";
                    //llvm::outs() << "CharDta:(" << *FullSourceLoc(expr_b, *this->sourceManager).getCharacterData() << ")\n";
                    if (!invalid) {
                        //continue;
                        if (tmpToken.getKind() == tok::semi) {
                            //llvm::outs() << "SEMI  "  << "\n";
                            isSemiFound = true;
                            break;
                        }
                    }
                    //expr_b = expr_b.getLocWithOffset(1);
                    expr_b = Lexer::getLocForEndOfToken(expr_b, 0, *this->sourceManager,
                                                        this->aSTContext->getLangOpts());
                } // End WHILE

                if (isSemiFound) {
                    CharSourceRange charSourceRange = CharSourceRange::getCharRange(expr->getBeginLoc(), expr_b);
                    if (charSourceRange.isValid()) {
                        const StringRef return_val_exp = Lexer::getSourceText(charSourceRange, *this->sourceManager,
                                                                              this->aSTContext->getLangOpts());
                        TheRewriter.InsertTextAfter(returnStmt->getBeginLoc(),
                                                    GET_LINE() + "fuSeBMC_return(" + return_val_exp.str() + ");" +
                                                    GET_LINE_E());
                        //llvm::outs() << "EXPRRRR:(" << return_val_exp.str() << ")\n";
                    }
                }

            }//if (expr)
            else // No expr : return;
                TheRewriter.InsertTextAfter(returnStmt->getBeginLoc(),
                                            GET_LINE() + "fuSeBMC_return(0);" + GET_LINE_E());
        }
    } else if (isa<CallExpr>(S)) {

    } else {

    }
}

void MyVisitor::handleInfiniteWhileLoop(WhileStmt *whileStmt, SourceLocation rParenLoc) {
    Expr *wCond = whileStmt->getCond();
    if (isa<IntegerLiteral>(wCond)) {
        IntegerLiteral *integerLiteral = cast<IntegerLiteral>(wCond);

        if (integerLiteral->getValue().getLimitedValue() == 1) {
            //std::cout << "ONEEEEE\n";
            for (Stmt::child_iterator i = whileStmt->child_begin(), e = whileStmt->child_end(); i != e; ++i) {
                Stmt *child = *i;
                if (!child) continue;
                if (isa<NullStmt>(child)) continue;
                if (containNonDetCall(child)) {
                    infinteWhileNum++;
                    ////std::cout << "NONDET\n";
                    //std::string fusebmc_while_counter= "fusebmc_" + std::to_string(infinteWhileNum);
                    //TheRewriter.InsertTextBefore(whileStmt->getBeginLoc(),
                    //		"for(int "+fusebmc_while_counter+"=0;"+fusebmc_while_counter+
                    //		"<"+myOptions->infiniteWhileLoopLimit +";"+fusebmc_while_counter+"++)//");
                    ////TheRewriter.InsertTextBefore(startLoc.getLocWithOffset(+1),"*/");
                    //SourceLocation tmpLoc= whileStmt->getBeginLoc();
                    //unsigned origStartLine = this->sourceManager->getSpellingLineNumber(tmpLoc);
                    //while(true)
                    //{
                    //unsigned startLine = this->sourceManager->getSpellingLineNumber(tmpLoc);
                    ////std::cout << "Current LiNE"<< startLine << "\n";
                    //if(startLine != origStartLine)
                    //{
                    //	//std::cout << "NEW LiNE"<< startLine << "\n";
                    //	origStartLine=startLine;
                    //	TheRewriter.InsertTextBefore(tmpLoc,"//");
                    //}
                    //if(tmpLoc==rParenLoc)
                    //{
                    //	TheRewriter.InsertTextBefore(tmpLoc.getLocWithOffset(1),"\n");
                    //	break;
                    //}
                    ////while (isWhitespace(*FullSourceLoc(tmpLoc, *this->sourceManager).getCharacterData()))
                    //tmpLoc = tmpLoc.getLocWithOffset(1);
                    //}
                }//
            }
        }
    }

}

template<typename IfOrWhileStmt>
SourceLocation MyVisitor::findRParenLocInIfOrWhile(const IfOrWhileStmt *stmt) {
    // Skip macros.
    if (stmt->getBeginLoc().isMacroID()) return SourceLocation();
    SourceLocation condEndLoc = stmt->getCond()->getEndLoc();
    if (const DeclStmt *conditionVariable = stmt->getConditionVariableDeclStmt())
        condEndLoc = conditionVariable->getEndLoc();
#ifdef MYDEBUG
    assert(condEndLoc.isValid());
#endif
    /*if(!condEndLoc.isValid())
    {
        stmt->dump();
        stmt->getLocStart().dump(sourceManager);
        exit(0);
    }*/
    SourceLocation pastCondEndLoc = Lexer::getLocForEndOfToken(condEndLoc, 0, *this->sourceManager,
                                                               this->aSTContext->getLangOpts());
    if (pastCondEndLoc.isInvalid())
        return SourceLocation();

    SourceLocation rParenLoc = skipCommentAndWhitespace(pastCondEndLoc);
    if (rParenLoc.isInvalid())
        return SourceLocation();

    tok::TokenKind TokKind = getTokenKindInLocation(rParenLoc);
    if (TokKind != tok::r_paren)
        return SourceLocation();

    return rParenLoc;
}

SourceLocation MyVisitor::skipCommentAndWhitespace(SourceLocation sourceLocation) {
#if MYDEBUG
    assert(sourceLocation.isValid());
#endif
    while (true) {
        while (isWhitespace(*FullSourceLoc(sourceLocation, *this->sourceManager).getCharacterData()))
            sourceLocation = sourceLocation.getLocWithOffset(1);
        tok::TokenKind tokenKind = getTokenKindInLocation(sourceLocation);
        if (tokenKind == tok::NUM_TOKENS || tokenKind != tok::comment)
            return sourceLocation;
        // Fast-forward current token.
        sourceLocation = Lexer::getLocForEndOfToken(sourceLocation, 0, *this->sourceManager,
                                                    this->aSTContext->getLangOpts());
    }
}

SourceLocation MyVisitor::skipCommentAndWhitespaceUntilSemi(SourceLocation sourceLocation) {
#if MYDEBUG
    assert(sourceLocation.isValid());
#endif
    while (true) {
        while (isWhitespace(*FullSourceLoc(sourceLocation, *this->sourceManager).getCharacterData()))
            sourceLocation = sourceLocation.getLocWithOffset(1);
        tok::TokenKind tokenKind = getTokenKindInLocation(sourceLocation);
        if (tokenKind == tok::NUM_TOKENS || tokenKind != tok::comment)
            if (tokenKind == tok::semi)
                return sourceLocation;
        // Fast-forward current token.
        sourceLocation = Lexer::getLocForEndOfToken(sourceLocation, 0, *this->sourceManager,
                                                    this->aSTContext->getLangOpts());
    }
}

SourceLocation MyVisitor::findEndLocation(SourceLocation lastTokenLoc) {
    SourceLocation tmpLocation = lastTokenLoc;
    // Loc points to the beginning of the last (non-comment non-ws) token
    // before end or ';'.
#if MYDEBUG
    assert(tmpLocation.isValid());
#endif
    bool skipEndWhitespaceAndComments = true;
    tok::TokenKind tokenKind = getTokenKindInLocation(tmpLocation);
    if (tokenKind == tok::NUM_TOKENS || tokenKind == tok::semi || tokenKind == tok::r_brace) {
        // If we are at ";" or "}", we found the last token. We could use as well
        // `if (isa<NullStmt>(S))`, but it wouldn't work for nested statements.
        skipEndWhitespaceAndComments = false;
    }
    tmpLocation = Lexer::getLocForEndOfToken(tmpLocation, 0, *this->sourceManager, this->aSTContext->getLangOpts());
    // Loc points past the last token before end or after ';'.
    if (skipEndWhitespaceAndComments) {
        tmpLocation = skipCommentAndWhitespace(tmpLocation);
        tok::TokenKind tokenKind = getTokenKindInLocation(tmpLocation);
        if (tokenKind == tok::semi)
            tmpLocation = Lexer::getLocForEndOfToken(tmpLocation, 0, *this->sourceManager,
                                                     this->aSTContext->getLangOpts());
    }
    while (true) {
#if MYDEBUG
        assert(tmpLocation.isValid());
#endif
        while (isHorizontalWhitespace(*FullSourceLoc(tmpLocation, *this->sourceManager).getCharacterData()))
            tmpLocation = tmpLocation.getLocWithOffset(1);
        if (isVerticalWhitespace(*FullSourceLoc(tmpLocation, *this->sourceManager).getCharacterData())) {
            // EOL, insert brace before.
            break;
        }
        tok::TokenKind tokenKind = getTokenKindInLocation(tmpLocation);
        if (tokenKind != tok::comment) {
            // Non-comment token, insert brace before.
            break;
        }
        SourceLocation tokenEndLoc = Lexer::getLocForEndOfToken(tmpLocation, 0, *this->sourceManager,
                                                                this->aSTContext->getLangOpts());
        SourceRange tokenRange(tmpLocation, tokenEndLoc);
        StringRef commentStr = Lexer::getSourceText(CharSourceRange::getTokenRange(tokenRange), *this->sourceManager,
                                                    this->aSTContext->getLangOpts());
        if (commentStr.startswith("/*") && commentStr.find('\n') != StringRef::npos) {
            // Multi-line block comment, insert brace before.
            break;
        }
        // else: Trailing comment, insert brace after the newline.
        // Fast-forward current token.
        tmpLocation = tokenEndLoc;
    }
    return tmpLocation;
}

/*bool MyVisitor::VisitFunctionDecl(FunctionDecl *func)
{
	string funcName = func->getNameInfo().getName().getAsString();
	string funcType = func->getReturnType().getAsString();
	cout << "Found function declaration: " << funcName << " of type " << funcType << "\n";
	return true;
}*/
bool MyVisitor::VisitDecl(Decl *decl) {
    if (decl->isFunctionOrFunctionTemplate() && decl->hasBody()) {
        const clang::FileEntry *f_entry = GetLocFileEntry(decl->getBeginLoc());
        const SourceManager &sourceManager = *TheHolder.SourceManager;

        //return sourceManager.getFileEntryForID(sourceManager.getFileID(loc));
#ifdef MYDEBUG
        std::cout << "We are in Func: " << decl->getAsFunction()->getNameAsString() << std::endl;
        std::cout << "FILE = " << f_entry->getName().str() << std::endl;
        std::cout << "getUID = " << f_entry->getUID() << std::endl;
        //std::cout << "MID = " << sourceManager.getMainFileID(). << std::endl;
        std::cout << "-------------------------------" << std::endl;
#endif
        if (f_entry->getUID() != mainFileID) return true;
    }
    if (decl->isFunctionOrFunctionTemplate() && decl->hasBody()) {
        this->current_func = decl->getAsFunction();
        if (myOptions->exportCallGraph)
            funcDeclList->addFuncDeclInfo(this->current_func->getNameAsString());
    } else {
        this->current_func = NULL;
    }


    if (decl->isFunctionOrFunctionTemplate() && decl->hasBody() && myOptions->addGoalAtEndOfFunc) {
#ifdef MYDEBUG
        std::cout << "We are in Func: " << decl->getAsFunction()->getNameAsString() << std::endl;
#endif
        //decl->PrintStats();
        //decl->dumpColor();

        Stmt *body = decl->getBody();
        // Iterate over the top level of statements;
        //not insert before
        // I don't know if we must check if the sub-statements include 'return'
        bool hasReturn = false;
        for (Stmt::child_iterator i = body->child_begin(), e = body->child_end(); i != e; ++i) {
            Stmt *currStmt = *i;
            if (isa<ReturnStmt>(currStmt)) {
                hasReturn = true;
                ReturnStmt *retStmt = cast<ReturnStmt>(currStmt);
                //std::cout << "BEGIN STMMT" << std::endl;
                //retStmt->dumpColor();
                //std::cout << "END STMMT" << std::endl;
                TheRewriter.InsertTextBefore(retStmt->getBeginLoc().getLocWithOffset(0), GET_LINE() +
                                                                                         goalCounter.GetNewGoalForFuncDecl(
                                                                                                 current_func,
                                                                                                 GoalType::END_OF_FUNCTION) +
                                                                                         "" +
                                                                                         GET_LINE_E());
            }
        }
        // NOTE : insert Before
        if (!hasReturn)
            TheRewriter.InsertTextBefore(body->getEndLoc().getLocWithOffset(0), GET_LINE() +
                                                                                goalCounter.GetNewGoalForFuncDecl(
                                                                                        current_func,
                                                                                        GoalType::END_OF_FUNCTION) +
                                                                                GET_LINE_E());
    }

    if (decl->isFunctionOrFunctionTemplate() && decl->hasBody()) {
        if (myOptions->addLabelInFunc) {
            std::string lbl = myOptions->GetLabelForFunc(this->current_func->getNameAsString());
            if (!lbl.empty()) {
                //std::cout <<"We have Label:" << lbl << std::endl;
                Stmt *body = decl->getBody();
                bool hasLbl = isLabelExistsInStement(body, lbl);
                //std::cout <<"hasLbl:" << hasLbl << std::endl;
                //std::cout <<"DONEEEEE:" << lbl << std::endl;
                if (!hasLbl) {
                    //std::cout <<"Label:" << lbl << " will be added in function:" << this->current_func->getNameAsString() << std::endl;
                    TheRewriter.InsertTextBefore(body->getBeginLoc().getLocWithOffset(1),
                                                 GET_LINE() + "\n" + lbl + ":;\n");
                }
            }
        }


        if (myOptions->addCommentInFunc) {
            std::string comment = myOptions->GetCommentForFunc(this->current_func->getNameAsString());
            if (!comment.empty()) {
                Stmt *body = decl->getBody();
                TheRewriter.InsertTextBefore(body->getBeginLoc().getLocWithOffset(1), GET_LINE() +
                                                                                      "\n//" + comment + "\n");
            }
        }


        // Add calls in Func.
        if (myOptions->addFuncCallInFunc) {
            std::string call = myOptions->GetCallForFunc(this->current_func->getNameAsString());
            if (!call.empty()) {
                Stmt *body = decl->getBody();
                TheRewriter.InsertTextBefore(body->getBeginLoc().getLocWithOffset(1), GET_LINE() + call + "();\n");
            }
            // Handle 'return' statements in main function.
            //std::cout << "WEEE are in: " << this->current_func->getNameAsString() << std::endl;
        }
    }
    if (decl->isFunctionOrFunctionTemplate() && decl->hasBody() &&
        myOptions->handleReturnInMain && this->current_func->getNameAsString() == "main") {
        Stmt *body = decl->getBody();
        //HandleReturnStmt(body);
        bool hasReturn = false;
        for (Stmt::child_iterator i = body->child_begin(), e = body->child_end(); i != e; ++i) {
            Stmt *child = *i;
            if (!child) continue;
            if (isa<ReturnStmt>(child)) {
                hasReturn = true;
                break;
            }
        }
        if (!hasReturn) {
            TheRewriter.InsertTextBefore(body->getEndLoc().getLocWithOffset(0), GET_LINE() +
                                                                                "fuSeBMC_return(0);" +
                                                                                GET_LINE_E());
        }
    }
    return true;
}


/** Defined in super class, will be automatically called*/

bool MyVisitor::VisitStmt(Stmt *s) {
    if (!s) return true;
    //llvm::outs() << "SSSSSSSSSSSSSSSs\r\n" ;
    const SourceManager &sourceManager = *TheHolder.SourceManager;
    //const ASTContext * aSTContext = TheHolder.ASTContext;

    if (myOptions->showParseTree) {
        s->dumpColor();
        s->getBeginLoc().dump(sourceManager);
        //llvm::outs() << "SSSSSSSSSSSSSSSs\r\n" ;
    }
    check(s);
    return true;
}

bool isLabelExistsInStement(Stmt *s, std::string &lbl) {
    if (!s || s == nullptr) return false;
    if (isa<LabelStmt>(s)) {
        LabelStmt *lblStmt = cast<LabelStmt>(s);
        if (lbl == lblStmt->getName())
            return true;
    }
    for (Stmt::child_iterator i = s->child_begin(), e = s->child_end(); i != e; ++i) {
        Stmt *currStmt = *i;
        if (isLabelExistsInStement(currStmt, lbl))
            return true;
    }
    return false;
}

/**
* Not used
*/
bool hasOneCompoundChild(Stmt *s) {
    // Else if child  of If,
    bool isIf = s && isa<IfStmt>(s);
    unsigned int count = 0;
    Stmt *child = nullptr;
    for (Stmt::child_iterator i = s->child_begin(), e = s->child_end(); i != e; ++i) {
        Stmt *ii = *i;
        if (!ii) continue;
        if (isa<NullStmt>(ii)) continue;
        if (isa<ImplicitCastExpr>(ii)) continue;
        if (isIf) {
            IfStmt *ifStmt = cast<IfStmt>(s);
            Stmt *Else = ifStmt->getElse();
            if (Else && Else == ii) continue;
        }
        count++;
        child = ii;
#ifdef MYDEBUG
        std::cout << "CHILD -->" << count << std::endl;
        //std::cout << typeid(*i).name() << std::endl;
        i->dumpColor();
        std::cout << "-----------------------" << std::endl;
#endif
    }
    if (count == 1) {
        //Stmt * child= *(s->child_begin());
        //if(child )
        if (isa<IfStmt>(child) || isa<ForStmt>(child) || isa<WhileStmt>(child) || isa<CXXForRangeStmt>(child)
            || isa<SwitchStmt>(child) || isa<DoStmt>(child)) {
#ifdef MYDEBUG
            std::cout << "Statement has one child: YES -->" << count << std::endl;
            s->dumpColor();
            std::cout << "-----------------------" << std::endl;
#endif
            return true;
        }
    }

#ifdef MYDEBUG
    std::cout << "Statement has one child: NO -->" << count << std::endl;
    s->dumpColor();
    std::cout << "-----------------------" << std::endl;
#endif
    return false;
}

/**
 * if(x){if(x);}  or if(x);else{if(x);}
 */
bool isCompoundWithOneIf(Stmt *s) {
    if (!isa<CompoundStmt>(s))
        return false;
    int counter = 0;
    Stmt *lastNotNullChild = nullptr;
    CompoundStmt *compoundStmt = cast<CompoundStmt>(s);
    for (Stmt::child_iterator i = compoundStmt->child_begin(), e = compoundStmt->child_end(); i != e; ++i) {
        Stmt *child = *i;
        if (!child) continue;
        if (isa<NullStmt>(child)) continue;
        //if(isa<IfStmt>(child))
        counter++;
        lastNotNullChild = child;
    }
    if (!lastNotNullChild)
        return false;
    if (counter == 1 && isa<IfStmt>(lastNotNullChild))
        return true;
    return false;
}

const clang::FileEntry *MyVisitor::GetLocFileEntry(SourceLocation loc) {
    const SourceManager &sourceManager = *TheHolder.SourceManager;
    return sourceManager.getFileEntryForID(sourceManager.getFileID(loc));
}