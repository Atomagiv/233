

#include <stdlib.h>
#include <stdio.h>
#include <algorithm>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"
#include <cstring>
#include <map>


extern int semant_debug;
extern char *curr_filename;
static ClassTable *curr_classtable;
static class__class *curr_class;
//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//

SymbolTable<Symbol, Symbol> *object_table;
std::map<Symbol, Feature> *method_table;
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}



ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr) {

    /* Fill this in */
    class_table = new std::map<Symbol, Class_>;
    install_basic_classes();
}

void ClassTable::install_basic_classes() {

    // The tree package uses these globals to annotate the classes built below.
   // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");
    
    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.
    
    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    // 
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
    class_(Object, 
           No_class,
           append_Features(
                   append_Features(
                           single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
                           single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
                   single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
           filename);

    // 
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class = 
    class_(IO, 
           Object,
           append_Features(
                   append_Features(
                           append_Features(
                                   single_Features(method(out_string, single_Formals(formal(arg, Str)),
                                              SELF_TYPE, no_expr())),
                                   single_Features(method(out_int, single_Formals(formal(arg, Int)),
                                              SELF_TYPE, no_expr()))),
                           single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
                   single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
           filename);  

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
    class_(Int, 
           Object,
           single_Features(attr(val, prim_slot, no_expr())),
           filename);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
    class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //       
    Class_ Str_class =
    class_(Str, 
           Object,
           append_Features(
                   append_Features(
                           append_Features(
                                   append_Features(
                                           single_Features(attr(val, Int, no_expr())),
                                           single_Features(attr(str_field, prim_slot, no_expr()))),
                                   single_Features(method(length, nil_Formals(), Int, no_expr()))),
                           single_Features(method(concat, 
                                      single_Formals(formal(arg, Str)),
                                      Str, 
                                      no_expr()))),
                   single_Features(method(substr, 
                              append_Formals(single_Formals(formal(arg, Int)), 
                                     single_Formals(formal(arg2, Int))),
                              Str, 
                              no_expr()))),
           filename);
}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream& ClassTable::semant_error(Class_ c)
{                                                             
    return semant_error(c->get_filename(),c);
}    

ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error()                  
{                                                 
    semant_errors++;                            
    return error_stream;
} 



/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */




void class__class::semant()
{
    curr_class = this;
    for(int i = features->first(); features->more(i); i = features->next(i)) 
    {
        features->nth(i)->semant();
    }
    return ;
}
//there is something wrong
void method_class::semant()
{
    cerr << "Method body has type " << expr->get_type() << " but function has type " << return_type << endl;//print err message 
    if (name == cool_abort || name == out_int || name == in_string || name == out_string ||
        name == in_int ||  name == length || name == concat || name == idtable.add_string("copy") 
        || name == type_name || name == substr)
        return;
    // object_table->enterscope();
    // for(int i = formals->first(); formals->more(i); i = formals->next(i))
    //     formals->nth(i)->semant();
    // expr->semant();
    // bool b1 = (false == curr_classtable->leq(expr->get_type(), return_type));
    // if (b1)
    // {
    //     curr_classtable->semant_error(curr_class);
    //     cerr << "Method body has type " << expr->get_type() << " but function has type " << return_type << endl;//print err message 
    // }
    // object_table->exitscope();
}

void attr_class::semant()
{
    bool b1 = (name == str_field || name == val);
    if (b1) return;
    init->semant();
    b1 = (false == curr_classtable->leq(init->get_type(), type_decl));
    if (b1) 
    {
        curr_classtable->semant_error(curr_class);
        cerr << "Initialization has type " << init->get_type() << " but attribute has type " << type_decl << endl;//print err message 
    } 
    return ;
}

void formal_class::semant()
{
    bool b1 = (type_decl != SELF_TYPE);
    if (b1) 
    {
        curr_classtable->ahead_class(type_decl);
        if (object_table->probe(name))
        {
            curr_classtable->semant_error(curr_class);
            cerr<<"Duplicate variable " << name << " exists in same scope"<< endl;//print err message 
        }
        if (name == self) 
        {
            curr_classtable->semant_error(curr_class);
            cerr<<"Variable cannot have name self"<< endl;//print err message 
        }
        object_table->addid(name, new Symbol(type_decl));
        return ;
    }
    curr_classtable->semant_error(curr_class);
    cerr << "Formal cannot have type SELF_TYPE" << endl;//print err message 
    return ;
}

void branch_class::semant()
{
    object_table->enterscope();
    curr_classtable->ahead_class(type_decl);
    if (object_table->probe(name))
    {
        curr_classtable->semant_error(curr_class);
        cerr<<"Duplicate variable " << name << " exists in same scope"<< endl;//print err message 
    }
    if (name == self) 
    {
        curr_classtable->semant_error(curr_class);
        cerr<<"Variable cannot have name self"<< endl;//print err message 
    }
    object_table->addid(name, new Symbol(type_decl));
    expr->semant();
    object_table->exitscope();
    return ;
}



Symbol ClassTable::ahead_attr(Symbol class_name, Symbol var_name)
{
    
    return ahead_class(class_name)->get_symbol(var_name);
}


void assign_class::semant()
{
    Symbol type_decl = curr_classtable->ahead_attr(curr_class->get_name(), name);
    expr->semant();
    if (!type_decl) 
    {
        type = Object;//let this err won't affect other parts
        curr_classtable->semant_error(curr_class);           
        cerr<<"Variable " << name << " does not exist in this scope"<< endl; //print err message 
    } 
    else {
        bool b1 = (curr_classtable->leq(expr->get_type(), type_decl));
        if (!b1) 
        {
            type = Object;//let this err won't affect other parts
            curr_classtable->semant_error(curr_class);           
            cerr<<"Expression type " << expr->get_type() << " does not inherit from " << type_decl<< endl; //print err message 
            return ;
        }
        type = expr->get_type();
    }
    return ;
}

Symbol dispatch_use(Expression expr, Symbol type_name, Symbol name, Expressions actual, Feature method)
{
    bool b2 = (method == NULL);
    if (b2) 
    {
        curr_classtable->semant_error(curr_class);           
        cerr<<"No method " << name << " in class " << type_name << " found"<< endl; //print err message 
        return Object;
    } else if (actual->len() != method->get_len() ) 
    {
        curr_classtable->semant_error(curr_class);           
        cerr<<"Method " << method->get_name() << " only has " << method->get_len() << " arguments"<< endl; //print err message 
        return Object;
    }
    for(int i = actual->first(); actual->more(i); i = actual->next(i)) 
    {
        actual->nth(i)->semant();
        b2 = (method == NULL||  method->get_len() <= i );
        if (!b2) 
        {
            bool b3 = (false == curr_classtable->leq(actual->nth(i)->get_type(), method->get_arg_type(i)));
            if (b3) 
            {
                curr_classtable->semant_error(curr_class);           
                cerr<<"Method " << method->get_name() << " argument " << i + 1<< " has type " << method->get_arg_type(i)<< endl; //print err message 
                return Object;
            }
        }
    }
    Symbol type = method->get_return_type();
    b2 = (type == SELF_TYPE);
    if (b2) type = expr->get_type();
    curr_classtable->ahead_class(type);
    return type;
}



void static_dispatch_class::semant()
{
    expr->semant();
    bool b1 = (curr_classtable->leq(expr->get_type(), type_name));
    if (b1) type = dispatch_use(expr, type_name, name, actual, curr_classtable->ahead_method(type_name, name));
    else {
        type = Object;//let this err won't affect other parts
        curr_classtable->semant_error(curr_class);           
        cerr<<"Expression of type " << expr->get_type() << " does not inherit from static dispatch type name " << type_name<< endl; //print err message 
        return ;
    }
}

Feature class__class::get_method(Symbol method)
{
    bool b1 = (method_table->find(method) == method_table->end());
    if (!b1) return NULL;
    b1 = (get_parent() != No_class);
    if (b1) return curr_classtable->ahead_class(get_parent())->get_method(method);
    return method_table->find(method)->second;
}

Feature ClassTable::ahead_method(Symbol class_name, Symbol method_name)
{
    bool b1 = (class_name == No_type);
    if (b1) class_name = curr_class->get_name();
    return ahead_class(class_name)->get_method(method_name);
}


void dispatch_class::semant()
{
    expr->semant();
    bool b1 = (curr_classtable->leq(expr->get_type(), type_name));
    if (!b1) 
    {
        type = Object;//let this err won't affect other parts
        curr_classtable->semant_error(curr_class);           
        cerr<<"Expression of type " << expr->get_type() << " does not inherit from static dispatch type name "<< type_name<< endl; //print err message 
        return ;
    } 
    type = dispatch_use(expr, type_name, name, actual, curr_classtable->ahead_method(type_name, name));
    return ;
}

Symbol ClassTable::lub(Symbol a, Symbol b)
{
    if (a == SELF_TYPE) 
        a = curr_class->get_name();
    if (b == SELF_TYPE) 
        b = curr_class->get_name();
    if (leq(a, b)) return b;
        else if (leq(b, a)) return a;
    if (ahead_class(a)->get_parent() != No_class) 
        return lub(ahead_class(a)->get_parent(), b);
    return Object;
}

bool ClassTable::leq(Symbol a, Symbol b)
{
    bool b1 = (a == No_type || b == No_type);
    if (b1) return true;
    b1 = (a != SELF_TYPE && b == SELF_TYPE);
    if (b1) return false;
    b1 = (a == SELF_TYPE);
    if (b1) a = curr_class->get_name();
    b1 = (b == SELF_TYPE);
    if (b1) b = curr_class->get_name();
    b1 = (a == b);
    if (b1) return true;
    b1 = (ahead_class(a)->get_parent() != No_class);
    if (b1) return leq(ahead_class(a)->get_parent(), b);
    return false;
}
void cond_class::semant()
{
    then_exp->semant();
    else_exp->semant();
    if (pred->get_type() == Bool)
    {
        type = curr_classtable->lub(then_exp->get_type(), else_exp->get_type());
    }
    type = Object;//let this err won't affect other parts
    curr_classtable->semant_error(curr_class);           
    cerr<<"Predicate of conditional is not of type Bool"<< endl; //print err message 
    return ;
}

void loop_class::semant()
{
    pred->semant();
    body->semant();
    if (pred->get_type() == Bool)
    {
        type = Object;
        return ;
    }
    type = Object;//let this err won't affect other parts
    curr_classtable->semant_error(curr_class);           
    cerr<<"Predicate does not have type Bool"<< endl; //print err message 
    return ;
}

Expression branch_class::get_expr()
{
    return expr;
}


void typcase_class::semant()
{
    expr->semant();
    for (int i = cases->first(); cases->more(i); i = cases->next(i))
    {
        cases->nth(i)->semant();
        bool b = (i != cases->first());
        if (b) type = curr_classtable->lub(type, cases->nth(i)->get_expr()->get_type());
            else type = cases->nth(i)->get_expr()->get_type();
    }
    for(int i = cases->first(); cases->more(i); i = cases->next(i)) 
    {
        for(int j = cases->next(i); cases->more(j); j = cases->next(j)) 
            {
                bool b = (cases->nth(i)->get_type_decl() == cases->nth(j)->get_type_decl());
                if (b) 
                {
                    curr_classtable->semant_error(curr_class);           
                    cerr<<"Branches in case statement have same type " << cases->nth(i)->get_type_decl()<< endl; //print err message 
                    return ;
                }
            }
    }
    type = Object;
    return ;
}

void block_class::semant()
{
    for(int i = body->first(); body->more(i); i = body->next(i)) 
    {
        body->nth(i)->semant();
        type = body->nth(i)->get_type();
    }
    return ;
}

void let_class::semant()
{
    init->semant();
    object_table->enterscope();
    if (object_table->lookup(type_decl) != NULL)
    {
        if (init->get_type() != No_type && init->get_type() != type_decl)
        {        
                type = Object;//let this err won't affect other parts
                curr_classtable->semant_error(curr_class);           
                cerr<<"Expression with type " << init->get_type() << " does not inherit from " << type_decl<< endl; //print err message 
                return ;
        }
    }
    else {
            type = Object;//let this err won't affect other parts
            curr_classtable->semant_error(curr_class);           
            cerr<<"Expression with type " << init->get_type() << " does not inherit from " << type_decl<< endl; //print err message 
            return ;
        }
    object_table->addid(identifier, &type_decl);
    body->semant();
    type = body->get_type();
    object_table->exitscope();
    return ;
}

void plus_class::semant()
//Both should be int
{
    e1->semant();
    e2->semant();
    if ( e1->get_type() == e2->get_type() )
    {
        bool b = (e1->get_type() != Int);
        if (b)
        {
            type = Object;//let this err won't affect other parts
            curr_classtable->semant_error(curr_class);           
            cerr<<"One of the expressions for multiply does not evaluate to Integer"<< endl; //print err message 
            return ;
        }
        type = Int;
        return ; 
    }
    type = Object;//let this err won't affect other parts
    curr_classtable->semant_error(curr_class);           
    cerr<<"One of the expressions for multiply does not evaluate to Integer"<< endl; //print err message 
    return ;
}

void sub_class::semant()
//Both should be int
{
    e1->semant();
    e2->semant();
    bool b1 = (e1->get_type() == e2->get_type() );
    if ( b1 )
    {
        bool b = (e1->get_type() != Int);
        if (b)
        {
            type = Object;//let this err won't affect other parts
            curr_classtable->semant_error(curr_class);           
            cerr<<"One of the expressions for multiply does not evaluate to Integer"<< endl; //print err message 
            return ;
        }
        type = Int;
        return ; 
    }
    type = Object;//let this err won't affect other parts
    curr_classtable->semant_error(curr_class);           
    cerr<<"One of the expressions for multiply does not evaluate to Integer"<< endl; //print err message 
    return ;
}

void mul_class::semant()
//Both should be int
{
    e1->semant();
    e2->semant();
    bool b = (e1->get_type() == e2->get_type()) ;
    if ( b )
    {
        bool b1 = (e1->get_type() != Int);
        if (b1)
        {
            type = Object;//let this err won't affect other parts
            curr_classtable->semant_error(curr_class);           
            cerr<<"One of the expressions for multiply does not evaluate to Integer"<< endl; //print err message 
            return ;
        }
        type = Int;
        return ; 
    }
    type = Object;//let this err won't affect other parts
    curr_classtable->semant_error(curr_class);           
    cerr<<"One of the expressions for multiply does not evaluate to Integer"<< endl; //print err message 
    return ;
}

void divide_class::semant()
//Both should be int
{
    e1->semant();
    e2->semant();
    if ( e1->get_type() == e2->get_type() )
    {
        if (e1->get_type() == Int)
        {
            type = Int;
            return ;
        }
    }
    type = Object;//let this err won't affect other parts
    curr_classtable->semant_error(curr_class);           
    cerr<<"One of the expressions for divide does not evaluate to Integer"<< endl; //print err message 
}

void neg_class::semant()
//it should be int
{
    e1->semant();
    if (e1->get_type() != Int) 
    {
        type = Object;//let this err won't affect other parts
        curr_classtable->semant_error(curr_class);           
        cerr<<"Expression does not have Integer type"<< endl; //print err message 
        return ;
    }
    type = Int;
    return ;
}

void lt_class::semant()
// both should be int
{
    e1->semant();
    e2->semant();
    if ( e1->get_type() == e2->get_type() )
    {
        if (e1->get_type() == Int)
        {
            type = Bool;
            return ;
        }
    }
    type = Object;//let this err won't affect other parts
    curr_classtable->semant_error(curr_class);           
    cerr<<"One of the expressions for lt does not evaluate to Integer"<< endl; //print err message 
    return ;
}

void eq_class::semant() 
// compare int or str or bool , can't be other type
{
    e1->semant();
    e2->semant();
    if (e1->get_type() == e1->get_type())
    {
        if (e1->get_type() == Int)
        {
            type = Bool;
            return ;
        }
        if (e1->get_type() == Str)
        {
            type = Bool;
            return ;
        }
        if (e1->get_type() == Bool)
        {
            type = Bool;
            return ;
        }
    }
    type = Object;//let this err won't affect other parts
    curr_classtable->semant_error(curr_class);           
    cerr<<"Expressions of types " << e1->get_type() << " and " << e2->get_type() << " cannot be compared"<< endl; //print err message  
    return ;  
}

void leq_class::semant()
//like lt
{
    e1->semant();
    e2->semant();
    if ( e1->get_type() == e2->get_type() )
    {
        if (e1->get_type() == Int)
        {
            type = Bool;
            return ;
        }
    }
    type = Object;//let this err won't affect other parts
    curr_classtable->semant_error(curr_class);           
    cerr<<"One of the expressions for leq does not evaluate to Integer"<< endl; //print err message 
    return ;
}

void comp_class::semant()
//check if it is a bool type
{
    e1->semant();
    if (e1->get_type()==Bool) 
    {
        type = Bool;
        return ;
    }
    type = Object;  //let this err won't affect other parts
    curr_classtable->semant_error(curr_class);           
    cerr<<"Expression does not have type Bool"<< endl;    //print err message    
    return ;                    
}

void int_const_class::semant()
//give the int type
{
    type = Int;
    return ;
}

void bool_const_class::semant() 
//give the bool type
{
    type = Bool;
    return ;
}


void string_const_class::semant() 
//give the str type
{
    type = Str;
    return ;
}

Symbol class__class::get_name()
{
  return name;
}

Class_ ClassTable::ahead_class(Symbol class_name)
{
    if (class_name==SELF_TYPE) class_name = curr_class->get_name();
    bool b=(class_table->end() == class_table->find(class_name));
    if (b) 
    {
        curr_classtable->semant_error(curr_class);           
        cerr<<"Type " << class_name << " does not exist"<< endl;    //print err message    
        assert(class_table->find(Object) != class_table->end());
    }
    if (!b) return class_table->find(class_name)->second;
        else return class_table->find(Object)->second;
}

void new__class::semant()
{
    curr_classtable->ahead_class(type_name);
    type = type_name;
    return ;
}

void isvoid_class::semant() 
{
    e1->semant();
    type = Bool;
    return ;
}

void no_expr_class::semant() 
{
    type = No_type;
    return ;
}

Symbol class__class::get_parent()
{
    return parent;
}

Symbol class__class::get_symbol(Symbol var)
{
    if (*object_table->lookup(var) != NULL)
    {
        return *object_table->lookup(var);
    }
    if (get_parent() != No_class) 
    {
      Class_ parent_class = curr_classtable->ahead_class(get_parent());
      return parent_class->get_symbol(var);
    } else {
      return NULL;
    }
    return var;
}
Symbol ClassTable::ahead_symbol(Symbol class_name, Symbol var_name)
{
    Class_ class_ = ahead_class(class_name);
    return class_->get_symbol(var_name);
}
//object_class wanted...

void object_class::semant()
{
    if (name == self)
    {
        type = SELF_TYPE;
        return ;
    }
    if (curr_classtable->ahead_symbol(curr_class->get_name(), name))
    {
        type = curr_classtable->ahead_symbol(curr_class->get_name(), name);
    }
    else {
        type = Object;  //let this err won't affect other parts
        curr_classtable->semant_error(curr_class);           
        cerr<<"Object " << name << " not declared in scope"<< endl;    //print err message                      
    }
    return ;
}


void program_class::semant()
{
    initialize_constants();

    /* ClassTable constructor may do some semantic analysis */
    ClassTable *classtable = new ClassTable(classes);
    for(int i = classes->first(); classes->more(i); i = classes->next(i)) 
    {
      classes->nth(i)->semant();
    }
    /* some semantic analysis code may go here */

    if (classtable->errors()) {
    cerr << "Compilation halted due to static semantic errors." << endl;
    exit(1);
    }
}

