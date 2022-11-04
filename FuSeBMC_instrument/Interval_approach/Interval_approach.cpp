#include "Interval_approach.h"

void goto_contractor() {
    goto_contractort gotoContractort();
}

void goto_contractort::get_contractors(clang::Expr *expr) {
    contractors.add_contractor(create_contractor_from_expr2t(expr), 0);
}

void goto_contractort::get_intervals() {
    //TODO: Intervals from Frama-c
}

void goto_contractort::parse_intervals(clang::Expr expr) {

}

void goto_contractort::insert_assume() {

}

void goto_contractort::apply_contractor() {
    Contractor *contractor = contractors.get_contractors();

    //Take the intersection of all contractors to perform Algorithm 2
    ibex::CtcFixPoint c_out(*contractor->get_outer());
    //Take the union of all contractors with complement constraints to perform Algorithm 3
    ibex::CtcFixPoint c_in(*contractor->get_inner());

    std::ostringstream oss;

    domains = map.create_interval_vector();

    oss << "Contractors applied:";
    oss << "\n\t- Domains (before): " << domains;
    auto X = domains;

    c_in.contract(X);

    oss << "\n\t- Domains (after): " << X;
    map.update_intervals(X);

    std::cout << oss.str() << std::endl;
}

ibex::Ctc *goto_contractort::create_contractor_from_expr2t(clang::Expr *expr) {
    ibex::Ctc *contractor = nullptr;
    auto base_object = get_base_object(expr);

    if (is_constraint_operator(expr)) {
        auto cons = create_constraint_from_expr2t(base_object);
        if (cons == nullptr)
            return nullptr;
        contractor = new ibex::CtcFwdBwd(*cons);
    } else {
        //std::shared_ptr<logic_2ops> logic_op;
        //logic_op = std::dynamic_pointer_cast<logic_2ops>(base_object);

        clang::BinaryOperator *binary_operator_expr = clang::cast<clang::BinaryOperator>(base_object);

        switch (binary_operator_expr->getOpcode()) {
            case clang::BinaryOperatorKind::BO_LAnd: {
                auto side1 = create_contractor_from_expr2t(binary_operator_expr->getLHS());
                auto side2 = create_contractor_from_expr2t(binary_operator_expr->getRHS());
                if (side1 != nullptr && side2 != nullptr)
                    contractor = new ibex::CtcCompo(*side1, *side2);
                break;
            }
            case clang::BinaryOperatorKind::BO_LOr: {
                auto side1 = create_contractor_from_expr2t(binary_operator_expr->getLHS());
                auto side2 = create_contractor_from_expr2t(binary_operator_expr->getRHS());
                if (side1 != nullptr && side2 != nullptr)
                    contractor = new ibex::CtcUnion(*side1, *side2);
                break;
            }
            case clang::BinaryOperatorKind::BO_EQ : {
                //std::shared_ptr<relation_data> rel;
                //rel = std::dynamic_pointer_cast<relation_data>(base_object);
                ibex::Function *f = create_function_from_expr2t(binary_operator_expr->getLHS());
                ibex::Function *g = create_function_from_expr2t(binary_operator_expr->getRHS());
                if (g == nullptr || f == nullptr)
                    return nullptr;
                auto *side1 = new ibex::NumConstraint(*vars, (*f)(*vars) > (*g)(*vars));
                auto *side2 = new ibex::NumConstraint(*vars, (*f)(*vars) < (*g)(*vars));
                auto *c_side1 = new ibex::CtcFwdBwd(*side1);
                auto *c_side2 = new ibex::CtcFwdBwd(*side2);
                contractor = new ibex::CtcUnion(*c_side1, *c_side2);
                break;
            }
                /*case expr2t::expr_ids::not_id:
                    //TODO: implement "not" flag  and process.
                    parse_error(base_object);
                    break;*/
            default:
                parse_error(base_object);
                break;
        }
    }
    return contractor;
}

bool goto_contractort::is_constraint_operator(clang::Expr *expr) {
    clang::Expr *e = get_base_object(expr);
    clang::BinaryOperator *b;
    if (clang::isa<clang::BinaryOperator>(e))
        b = clang::cast<clang::BinaryOperator>(e);
    return (b->isComparisonOp() && !(b->getOpcode() == clang::BinaryOperatorKind::BO_NE)) || b->isAdditiveOp() ||
           b->isMultiplicativeOp();
}

ibex::NumConstraint *
goto_contractort::create_constraint_from_expr2t(clang::Expr *expr) {
    ibex::NumConstraint *c;

    //if (is_unsupported_operator_in_constraint(expr)) {
    auto base_object = get_base_object(expr);
    if(!clang::isa<clang::BinaryOperator>(base_object)){
        parse_error(base_object);
        return nullptr;
    }
    clang::BinaryOperator *rel = clang::cast<clang::BinaryOperator>(base_object);

    if(!rel->isComparisonOp() || rel->getOpcode() == clang::BinaryOperatorKind::BO_NE)
        return nullptr;
    //std::shared_ptr<relation_data> rel;
    //rel = std::dynamic_pointer_cast<relation_data>(get_base_object(expr));

    ibex::Function *f, *g;
    f = create_function_from_expr2t(rel->getLHS());
    g = create_function_from_expr2t(rel->getRHS());
    if (f == nullptr || g == nullptr)
        return nullptr;
    //TODO: implement "not" flag  and process.
    switch (rel->getOpcode()) {
        case clang::BinaryOperatorKind::BO_GE:
            c = new ibex::NumConstraint(*vars, (*f)(*vars) >= (*g)(*vars));
            break;
        case clang::BinaryOperatorKind::BO_GT:
            c = new ibex::NumConstraint(*vars, (*f)(*vars) > (*g)(*vars));
            break;
        case clang::BinaryOperatorKind::BO_LE:
            c = new ibex::NumConstraint(*vars, (*f)(*vars) <= (*g)(*vars));
            break;
        case clang::BinaryOperatorKind::BO_LT:
            c = new ibex::NumConstraint(*vars, (*f)(*vars) < (*g)(*vars));
            break;
        case clang::BinaryOperatorKind::BO_EQ:
            c = new ibex::NumConstraint(*vars, (*f)(*vars) = (*g)(*vars));
            break;
        default:
            return nullptr;
    }
    return c;
}

/*
bool goto_contractort::is_unsupported_operator_in_constraint(
        clang::Expr *expr) {
    clang::Expr *e = get_base_object(expr);
    clang::BinaryOperator *b;
    if (isa<clang::BinaryOperator>(e)) {
        b = cast<clang::BinaryOperator>(e);
        return b->isAdditiveOp() || b->isMultiplicativeOp() || !(b->getOpcode() == clang::BinaryOperatorKind::BO_NE) ||
    }
    return is_arith_expr(e) || is_constant_number(e) || is_symbol2t(e) ||
           is_notequal2t(e) || is_not2t(e) || is_modulus2t(e) || is_or2t(e) ||
           is_and2t(e);
}
*/

ibex::Function *goto_contractort::create_function_from_expr2t(clang::Expr *expr) {
    ibex::Function *f = nullptr;
    ibex::Function *g, *h;

    auto base_object = get_base_object(expr);
    if(!clang::isa<clang::BinaryOperator>(base_object))
    {
        parse_error(expr);
        return nullptr;
    }

    switch (base_object->getStmtClass()) {
        case clang::Stmt::BinaryOperatorClass: {
            clang::BinaryOperator *binaryOperator = clang::cast<clang::BinaryOperator>(get_base_object(expr));
            if (!binaryOperator->isMultiplicativeOp() && !binaryOperator->isAdditiveOp()) {
                parse_error(expr);
                return nullptr;
            }

            //arith_op = std::dynamic_pointer_cast<arith_2ops>(expr);
            g = create_function_from_expr2t(binaryOperator->getLHS());
            h = create_function_from_expr2t(binaryOperator->getRHS());
            if (g == nullptr || h == nullptr)
                return nullptr;

            switch (binaryOperator->getOpcode()) {
                case clang::BinaryOperatorKind::BO_Add:
                    f = new ibex::Function(*vars, (*g)(*vars) + (*h)(*vars));
                    break;
                case clang::BinaryOperatorKind::BO_Sub:
                    f = new ibex::Function(*vars, (*g)(*vars) - (*h)(*vars));
                    break;
                case clang::BinaryOperatorKind::BO_Mul:
                    f = new ibex::Function(*vars, (*g)(*vars) * (*h)(*vars));
                    break;
                case clang::BinaryOperatorKind::BO_Div:
                    f = new ibex::Function(*vars, (*g)(*vars) / (*h)(*vars));
                    break;
                default:
                    return nullptr;
            }
            break;
        }
        case clang::Stmt::UnaryOperatorClass: {
            clang::UnaryOperator *unaryOperator = clang::cast<clang::UnaryOperator>(base_object);
            if(unaryOperator->getOpcode() != clang::UnaryOperatorKind::UO_Minus) {
                parse_error(base_object);
                return nullptr;
            }
            h = create_function_from_expr2t(unaryOperator->getSubExpr());
            f = new ibex::Function(*vars, -(*h)(*vars));
            break;
        }
        case clang::Stmt::DeclRefExprClass: {
            clang::DeclRefExpr *declRefExpr = clang::cast<clang::DeclRefExpr>(base_object);
            if(auto var = clang::dyn_cast<clang::VarDecl>(declRefExpr->getDecl())) {
                int index = create_variable_from_expr2t(var);
                if (index != CspMap::NOT_FOUND) {
                    f = new ibex::Function(*vars, (*vars)[index]);
                } else {
                    std::cout << "ERROR: MAX VAR SIZE REACHED" << std::endl;
                    return nullptr;
                }
            }
            std::cout << "not an integer variable"<< std::endl;
            return nullptr;
            break;
        }
        case clang::Stmt::IntegerLiteralClass: {
            auto x = clang::cast<clang::IntegerLiteral>(base_object);
            const ibex::ExprConstant &c =
                    ibex::ExprConstant::new_scalar(x->getValue().getSExtValue());
            f = new ibex::Function(*vars, c);
            break;
        }
        default:
            f = nullptr;
    }

    return f;
}

int goto_contractort::create_variable_from_expr2t(clang::VarDecl *expr) {
        std::string var_name = expr->getNameAsString();
        int index = map.add_var(var_name, expr);
        return index;
}

void goto_contractort::parse_error(clang::Expr *expr) {
    std::ostringstream oss;
    oss << expr->getStmtClassName();
    oss << " Expression is complex, skipping this assert.\n";
    std::cout << oss.str() << std::endl;
}

bool goto_contractort::initialize_main_function_loops() {
    return true;
}

clang::Expr *goto_contractort::get_base_object(clang::Expr *expr) {
    ;
    if (clang::isa<clang::CastExpr>(expr)) {
        clang::CastExpr *e = clang::cast<clang::CastExpr>(expr);
        return e->getSubExpr();
    }
    return expr;
}

const ibex::Interval &vart::getInterval() const {
    return interval;
}

size_t vart::getIndex() const {
    return index;
}

vart::vart(const string &varName, clang::VarDecl *symbol, const size_t &index) {
    this->var_name = varName;
    this->symbol = symbol;
    this->index = index;
    interval_changed = false;
}

void vart::setInterval(const ibex::Interval &interval) {
    this->interval = interval;
}

bool vart::isIntervalChanged() const {
    return interval_changed;
}

void vart::setIntervalChanged(bool intervalChanged) {
    interval_changed = intervalChanged;
}

clang::VarDecl *vart::getSymbol() const {
    return symbol;
}
