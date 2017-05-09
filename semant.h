#ifndef SEMANT_H_
#define SEMANT_H_

#include <assert.h>
#include <iostream>  
#include "cool-tree.h"
#include "stringtab.h"
#include "symtab.h"
#include "list.h"
#include <map>

#define TRUE 1
#define FALSE 0

class ClassTable;
typedef ClassTable *ClassTableP;

// This is a structure that may be used to contain the semantic
// information such as the inheritance graph.  You may use it or not as
// you like: it is only here to provide a container for the supplied
// methods.

class ClassTable {
private:
  int semant_errors;
  void install_basic_classes();
  ostream& error_stream;
  std::map<Symbol, Class_> *class_table;

public:
  ClassTable(Classes);
  Symbol lub(Symbol a, Symbol b);
  bool leq(Symbol a, Symbol b);
  int errors() { return semant_errors; }
  Class_ ahead_class(Symbol class_name);
  Symbol ahead_symbol(Symbol class_name, Symbol var_name);
  Symbol ahead_attr(Symbol class_name, Symbol var_name);
  ostream& semant_error();
  ostream& semant_error(Class_ c);
  ostream& semant_error(Symbol filename, tree_node *t);
  Feature ahead_method(Symbol class_name, Symbol method_name);
};


#endif
