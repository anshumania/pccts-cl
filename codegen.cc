/* ===== semantic.c ===== */
#include <string>
#include <iostream>
#include <map>
#include <list>
#include <vector>

using namespace std;

#include <stdio.h>
#include <stdlib.h>

#include "ptype.hh"
#include "symtab.hh"
#include "codegest.hh"

#include "myASTnode.hh"

#include "util.hh"
#include "semantic.hh"

#include "codegen.hh"

static const int NONE = 0;
static const int INFO = 2;
static const int DEBUG= 3;
static const int SPEC =1;

static const int loglevel = SPEC;

#define logable(a) (a<=loglevel)



// symbol table with information about identifiers in the program
// declared in symtab.cc
extern symtab symboltable;

// When dealing with a list of instructions, it contains the maximum auxiliar space
// needed by any of the instructions for keeping non-referenceable non-basic-type values.
int maxoffsetauxspace;

// When dealing with one instruction, it contains the auxiliar space
// needed for keeping non-referenceable values.
int offsetauxspace;

// For distinghishing different labels for different if's and while's.
int newLabelWhile(bool inicialitzar = false){
  static int comptador = 1;
  if (inicialitzar) comptador = 0;
  return comptador++;
}

int newLabelIf(bool inicialitzar = false){
  static int comptador = 1;
  if (inicialitzar) comptador = 0;
  return comptador++;
}


codechain indirections(int jumped_scopes,int t)
{
  codechain c;
  if (jumped_scopes==0) {
    c="aload static_link t"+itostring(t);
  }
  else {
    c="load static_link t"+itostring(t);
    for (int i=1;i<jumped_scopes;i++) {
      c=c||"load t"+itostring(t)+" t"+itostring(t);
    }
  }
  return c;
}

int compute_size(ptype tp)
{
  if (isbasickind(tp->kind)) {
    tp->size=4;
  }
  else if (tp->kind=="array") {
    tp->size=tp->numelemsarray*compute_size(tp->down);
  }
  else if (tp->kind=="struct") {
    tp->size=0;
    for (list<string>::iterator it=tp->ids.begin();it!=tp->ids.end();it++) {
      tp->offset[*it]=tp->size;
      tp->size+=compute_size(tp->struct_field[*it]);
    }
  }
  return tp->size;
}

void gencodevariablesandsetsizes(scope *sc,codesubroutine &cs,bool isfunction=0)
{
  if (isfunction) cs.parameters.push_back("returnvalue");
  for (list<string>::iterator it=sc->ids.begin();it!=sc->ids.end();it++) {
  if(logable(DEBUG))
	  cout<<"[gencodevariablesandsetsizes]sc->m[*it]"<< sc->m[*it].kind << endl;

    if (sc->m[*it].kind=="idvarlocal") {
      variable_data vd;
      vd.name="_"+(*it);
      vd.size=compute_size(sc->m[*it].tp);
      cs.localvariables.push_back(vd);
    } else if (sc->m[*it].kind=="idparval" || sc->m[*it].kind=="idparref") {

      compute_size(sc->m[*it].tp);
      cs.parameters.push_back("_"+(*it));
    } else if (sc->m[*it].kind=="idfunc") {

      // Here it is assumed that in tp->right is kept the return value type
      // for the case of functions. If this is not the case you must
      // change this line conveniently in order to force the computation
      // of the size of the type returned by the function.
      compute_size(sc->m[*it].tp->right);
    } else if (sc->m[*it].kind=="idproc") {
          //cout<<"[gencodevariablesandsetsizes]nothing to be done"<<endl;
      // Nothing to be done.
    }
  }
  cs.parameters.push_back("static_link");
}

codechain GenLeft(AST *a,int t);
codechain GenRight(AST *a,int t);

void CodeGenRealParams(AST *a,ptype tp,codechain &cpushparam,codechain &cremoveparam,int t)
{
  if (!a) return;
  if(logable(DEBUG))
    cout<<"[CodeGenRealParams] Starting with node \""<<a->text <<" "<<a->kind<<"\"" << " at line " << a->line<<endl;



  //...to be done.


 // fetch the parameters	
 AST *params = a->down->right->down ; 

 for( tp = tp->down ; params != 0 ; params = params->right , tp = tp->right )
 	{
		//cout << "parameter type kind " << tp->kind << endl;
		if(tp->kind == "parref")
		{
		  if(logable(DEBUG))
			cout<<"Parameter by reference" << endl;
  	          cpushparam = cpushparam || GenLeft(params, t) || "pushparam t" + itostring(t);
		}
		else if (tp->kind == "parval")
		{
		 if(logable(DEBUG))
			cout<<"Parameter by value" << endl;

		   cpushparam = cpushparam || GenRight(params, t) || "pushparam t" + itostring(t);
		}
		cremoveparam = cremoveparam || "killparam" ;
	}
   // now fetch the static link .
   // use the function jumped_scopes to find the nth level
   // then use the indirections function to get the scope 
   // of the correct static link
	int nLevel = symboltable.jumped_scopes(a->down->text);
	cpushparam = cpushparam || indirections(nLevel,t);
	cremoveparam = cremoveparam || "killparam" ;
	cpushparam = cpushparam || "pushparam t" + itostring(t);
   
  //cout<<"Ending with node \""<<a->kind<<"\""<<endl;
}

// ...to be completed:
codechain GenLeft(AST *a,int t)
{
  codechain c;

  if (!a) {
    return c;
  }

// cout<<"Starting with node \""<<a->kind<<"\"" << "at line " << a->line <<endl;
  if (a->kind=="ident") {

	 // is in a parent scope
	if(symboltable.jumped_scopes(a->text) > 0 ) 
	{

	        // is a parameter by reference then
                // load the static link  ; add the offset and load the value	
		if(symboltable[a->text].kind == "idparref")
		{
			c = "load static_link t" + itostring(t) ||
				"addi t" + itostring(t) + " offset(" + symboltable.idtable(a->text) + ":_" + a->text + ") t" + itostring(t) ||
					"load t" + itostring(t) + " t" + itostring(t);
		}	
		// is a parameter by value then
		// load the static link ; for the number of jumped scopes load the value ;
                // add the offset
		else if(symboltable[a->text].kind == "idparval")
		{
			c = "load static_link t" + itostring(t) ;
			for(int i=1 ; i < symboltable.jumped_scopes(a->text); i++)
			{
				c = c || "load t" + itostring(t) + " t" + itostring(t);
			}
			c = c || "addi t" + itostring(t) + " offset(" + symboltable.idtable(a->text) + ":_" + a->text + ") t" + itostring(t);
				
		}
		// is a global parameter => not a value by ref or parameter
		else if (symboltable[a->text].kind != "idparref" && symboltable[a->text].kind != "idparval")
		{
			c = "load static_link t" + itostring(t);
			for(int i=1 ; i < symboltable.jumped_scopes(a->text) ; i++ )
			{
				c = c || "load t" + itostring(t) + " t" + itostring(t);
			}
			c = c || "addi t" + itostring(t) + " offset(" + symboltable.idtable(a->text) + ":_" + a->text + ") t" + itostring(t);
		}	
	}
	// is in the current scope
	else
        {
		if(symboltable[a->text].kind == "idparval")
		{
			// is a basic type
			if(isbasickind(a->tp->kind))
				c = "aload _" + a->text + " t" + itostring(t);
			// is a local variable
			else
				c = "load _" + a->text + " t" + itostring(t);
		}
		// is a parameter by reference		
		else if(symboltable[a->text].kind == "idparref")
			c = "load _" + a->text + " t" + itostring(t);
		// is a complex type
   		else  
			  c="aload _"+a->text+" t"+itostring(t);
  	}	
 }
  else if (a->kind=="."){
    c=GenLeft(child(a,0),t)||
      "addi t"+itostring(t)+" "+
      itostring(child(a,0)->tp->offset[child(a,1)->text])+" t"+itostring(t);
  }
  // array access
  else if (a->kind == "[")
	{
		/*
		  multiply the index into the array
		  with the size of the type of the array
		  then add this offse to the base address		
		*/
		c = GenLeft(a->down,t) ||
			GenRight(a->down->right,t+1) ||
			"muli t" + itostring(t+1) + " " + itostring(compute_size(a->tp)) + " t" + itostring(t+1) ||
			"addi t" + itostring(t) + " t" + itostring(t+1) + " t" + itostring(t);
	}

  
	
  else {
    cout<<"[BIG PROBLEM! - GENLEFT] No case defined for kind "<<a->kind << " at line " << a->line <<endl;
  }
  //cout<<"Ending with node \""<<a->kind<<"\""<<endl;
  return c;
}


// ...to be completed:
codechain GenRight(AST *a,int t)
{
  codechain c;

  if (!a) {
    return c;
  }

  if (logable(DEBUG))
  	cout<<"[GENRIGHT - START]Starting with node \""<<a->text <<" "<<a->kind<<"\"" << " at line " << a->line<<endl;
  if (a->ref) {
    
  // is not a parameter by reference and is of basic kind
  if (a->kind=="ident" && symboltable.jumped_scopes(a->text)==0 &&
	isbasickind(symboltable[a->text].tp->kind) && symboltable[a->text].kind!="idparref") {
	if(logable(DEBUG))
		cout<<" Is of basic kind " << symboltable[a->text].tp->kind << " and is not a parameter by reference"<<symboltable[a->text].kind << endl;
	c="load _"+a->text+" t"+itostring(t);
    }
    else if (isbasickind(a->tp->kind)) {
     if(logable(DEBUG))
	      cout<<"isbasickind" << a->tp->kind << " at line " << a->line << endl;
      c=GenLeft(a,t)||"load t"+itostring(t)+" t"+itostring(t);
    }

    // not of basic type utilize the auxillary space	
    else {//...to be done
	
	c = GenLeft(a,t+1) ||
		"aload aux_space t" + itostring(t) ||
		"addi t" + itostring(t) + " " + itostring(offsetauxspace) + " t" + itostring(t) ||
		"copy t" + itostring(t+1) + " t" + itostring(t) + " " + itostring(a->tp->size) ;
	offsetauxspace += a->tp->size ;

	if(logable(DEBUG))
		cout<<"Not of basic type ; utilize the auxillary space " << endl ;
	
    }    
  } 
  else if (a->kind=="intconst") {
    c="iload "+a->text+" t"+itostring(t);
  }
  else if (a->kind=="+") {
    c=GenRight(child(a,0),t)||
      GenRight(child(a,1),t+1)||
      "addi t"+itostring(t)+" t"+itostring(t+1)+" t"+itostring(t);
  }
 // unary operator
 else if (a->kind == "-" && a->down->right == 0)
	{
		c = GenRight(a->down,t) || "mini t" + itostring(t) + " t" + itostring(t) ;
	}
  // substraction
 else if (a->kind == "-" && a->down->right !=0)
	{
		c = GenRight(child(a,0),t) ||
			GenRight(child(a,1),t+1) ||
			"subi t" + itostring(t) + " t" + itostring(t+1) + " t" + itostring(t) ;
	}

  // multiplication
  else if (a->kind == "*")
	{
		c = GenRight(child(a,0),t) ||
			GenRight(child(a,1),t+1) ||
			"muli t" + itostring(t) + " t" + itostring(t+1) + " t" + itostring(t);
	}
  // division
  else if ( a->kind == "/")
	{
		c = GenRight(child(a,0),t) ||
			GenRight(child(a,1),t+1) ||
			"divi t" + itostring(t) + " t" + itostring(t+1) + " t" + itostring(t);
	}

  // true
  else if (a->kind == "true")
	{
		c = "iload 1 t"+itostring(t);
	}   
  // false
  else if (a->kind == "false")
	{
		c = "iload 0 t"+itostring(t);
	}
  // lesser than
  else if (a->kind == "<" )
	{
		c = GenRight(a->down,t) || 
			GenRight(a->down->right,t+1) ||
			"lesi t" + itostring(t) + " t" + itostring(t+1) + " t" + itostring(t);
	}
  // greater than
  else if (a->kind == ">" )
	{
		c = GenRight(a->down,t) || 
			GenRight(a->down->right,t+1) || 
			"grti t" + itostring(t) + " t" + itostring(t+1) + " t" + itostring(t);
	}

  // equality
  else if (a->kind == "=")
	{
		c =  GenRight(a->down,t) || 
			GenRight(a->down->right,t+1) ||
			"equi t" + itostring(t) + " t" + itostring(t+1) + " t" + itostring(t);
	}
  // and
  else if (a->kind == "and")
	{
		c = GenRight(a->down,t) || 
			GenRight(a->down->right,t+1) || 
			"land t" + itostring(t) + " t" + itostring(t+1) + " t" + itostring(t);
	}
  // not
  else if (a->kind == "not")
	{
		c = GenRight(a->down,t) ||
			"lnot t" + itostring(t) + " t" + itostring(t) ;
	}
  // or 
  else if (a->kind == "or")
	{
		c = GenRight(a->down,t) ||
			GenRight(a->down->right,t+1) || 
			"loor t" + itostring(t) + " t" + itostring(t+1) + " t" + itostring(t);
	}

  else if (a->kind == "(")
	{
	  codechain pushparam, popparam;
	  // this is the case for a function writeln(func(x)) : jp27
          // check for the return type 
          // if basic
	  if(isbasickind(symboltable[a->down->text].tp->right->kind))
		{
			if(logable(DEBUG))	
				cout<<" The return type is basic " << a->down->text <<":" << symboltable[a->down->text].tp->right->kind <<  endl;
			//make space for the result
			pushparam = "pushparam 0";
			//generate the parameters for the function 
			CodeGenRealParams(a,symboltable[a->down->text].tp,pushparam,popparam,t);
			//fetch the result
			popparam = popparam || "popparam t" + itostring(t);
		}
	 // the return type is an array or struct (not basic)
	  else
		{
			if(logable(DEBUG))
				cout<<" The return type is complex " << endl;
			// load the auxillary space to store the value of the result
			pushparam = "aload aux_space t" + itostring(t) ||
					"addi t" + itostring(t) + " " + itostring(offsetauxspace) + " t" + itostring(t) ||
					"pushparam t" + itostring(t);	
			// get the new auxillary offset as the size of the return type
			offsetauxspace += compute_size(symboltable[a->down->text].tp->right);	
			// generate the parameters ( +1 for the return type )
			CodeGenRealParams(a,symboltable[a->down->text].tp, pushparam, popparam, t+1);
			// just pop all the params
			popparam = popparam || "killparam";
		}
	  string funcCall = "call " + symboltable.idtable(a->down->text) + "_" + a->down->text;
	  c = pushparam || funcCall || popparam ;
	} 

  // array access
  else if (a->kind == "[")
	{
		// offset by the index into the array and add the offset 
		c = GenLeft(a->down,t) || 
			GenRight(a->down,t+1) || 
			"muli t" + itostring(t+1) + " " + itostring(a->down->tp->down->size) + " t" + itostring(t+1) ||
			"addi t" + itostring(t) + " t" + itostring(t+1) + " t" + itostring(t) ;
	}

  // struct access
  else if (a->kind == "." )
	{
		c = GenRight(a->down,t) || 
			"addi t" + itostring(t) + " " + itostring(a->down->tp->offset[a->down->right->text]) + " t" + itostring(t) ;
	}
  
  else {
	cout<<"[BIG PROBLEM! - GENRIGHT]  No case defined for kind "<<a->kind << " at line " << a->line <<endl;
      }
  //cout<<"[GENRIGHT - END] Ending with node \""<<a->kind<<"\""<<endl;
  return c;
}

// ...to be completed:
codechain CodeGenInstruction(AST *a,string info="")
{
  codechain c;

  if (!a) {
    return c;
  }
  if(logable(DEBUG))
  	cout<<"[START - CodeGenInstruction] Starting with node \""<<a->text<<" "<<a->kind<<"\"" << " at line " << a->line<<endl;
  offsetauxspace=0;
  if (a->kind=="list") {
    for (AST *a1=a->down;a1!=0;a1=a1->right) {
      c=c||CodeGenInstruction(a1,info);
    }
  }
  else if (a->kind==":=") {
    if (isbasickind(child(a,0)->tp->kind)) {
      c=GenLeft(child(a,0),0)||GenRight(child(a,1),1)||"stor t1 t0";
    }
    else if (child(a,1)->ref) {
      c=GenLeft(child(a,0),0)||GenLeft(child(a,1),1)||"copy t1 t0 "+itostring(child(a,1)->tp->size);
    }
    else {
      c=GenLeft(child(a,0),0)||GenRight(child(a,1),1)||"copy t1 t0 "+itostring(child(a,1)->tp->size);
    }
  }
  if( offsetauxspace > maxoffsetauxspace)
  {
	maxoffsetauxspace = offsetauxspace ; 
  }
 
  else if (a->kind=="write" || a->kind=="writeln") {
    if (child(a,0)->kind=="string") {
      //...to be done.
	// if its a string just spurt it out !
	c = "wris " + a->down->text;
    } 
    else {//Exp
      c=GenRight(child(a,0),0)||"wrii t0";
    }

    if (a->kind=="writeln") {
      c=c||"wrln";
    }
  }
 else if (a->kind == "while")
	{
		/* create a while label
		 generate the expression
		 false jump to endOfWhile
                 generate instructions within the while block
		 unconditional jump to while
                 the end of while		
                */
		int whileLabel = newLabelWhile();
		c = "etiq while_" + itostring(whileLabel) ||
			GenRight(a->down,0) ||
			"fjmp t0 endwhile_" + itostring(whileLabel) ||
			CodeGenInstruction(a->down->right,"instruction") ||
			"ujmp while_" + itostring(whileLabel) ||
			"etiq endwhile_" + itostring(whileLabel) ;
		
	}
  else if (a->kind == "if")
	{
	       /*
		if expr then instr else instr	
		*/
		if(logable(DEBUG))
			cout<<"found If for line number " << a->line << endl;
		int ifLabel = newLabelIf();
		// has else	
		if(a->down->right->right)
		{
			c = GenRight(a->down,0)  || 
				"fjmp t0 else_" + itostring(ifLabel) ||
				CodeGenInstruction(a->down->right,"instruction") || 
				"ujmp endif_" + itostring(ifLabel) ||
				"etiq else_" + itostring(ifLabel) || 
				CodeGenInstruction(a->down->right->right,"instruction") ||
				"etiq endif_" + itostring(ifLabel);
		}
		// without else  : if expr then instr
		else
		{
			c = GenRight(a->down,0) ||
				"fjmp t0 endif_" + itostring(ifLabel) ||
				CodeGenInstruction(a->down->right,"instruction") ||
				"etiq endif_" + itostring(ifLabel);
		}
	}

   // procedure call
    else if (a->kind == "(")
	{
		/*
			(
			| ident
			| | list of params
		*/
		codechain pushparam, popparam ;
		CodeGenRealParams(a,a->tp,pushparam,popparam,0);
		string procCall = "call " + symboltable.idtable(a->down->text) + "_" + a->down->text;
		c = pushparam || procCall || popparam ;
			
	}
  //cout<<"Ending with node \""<<a->kind<<"\""<<endl;
  if(logable(DEBUG))
    cout<<"[END - CodeGenInstruction] Ending with node "<<a->text<<" "<<a->kind<< " at line number " << a->line << endl;

  return c;
}

void CodeGenSubroutine(AST *a,list<codesubroutine> &l)
{
  codesubroutine cs;

  if(logable(DEBUG))
	cout<<"[CodeGenSubroutine] Starting with node \""<<a->kind<<"\""<< "at line " << a->line<<endl;
  string idtable=symboltable.idtable(child(a,0)->text);
  cs.name=idtable+"_"+child(a,0)->text;
  symboltable.push(a->sc);
  symboltable.setidtable(idtable+"_"+child(a,0)->text);

  //...to be done.

  gencodevariablesandsetsizes(a->sc, cs, a->kind == "function" ? 1 : 0);
  // generate other subroutines within the procedure
  for(AST *sub = a->down->right->right->down; sub != 0 ; sub = sub->right)
	CodeGenSubroutine(sub,l);

  maxoffsetauxspace = 0 ;
  newLabelIf(true);
  newLabelWhile(true);
  
  // for this codesubroutine attach the associated codechain
  // simply put get generate the code for the instructions
  cs.c = CodeGenInstruction(a->down->right->right->right);
 
  if(a->kind ==  "function" )
  {
	//cout<<"HANDLE CASE FOR FUNCTION"<<endl;
	// if the return type of the function is of basic type
	if( isbasickind(a->down->right->right->right->right->tp->kind))	
		cs.c = cs.c || GenRight(a->down->right->right->right->right,0) || 
				"stor t0 returnvalue";
	// the return type of the function is of non-basic type
	else
	{
		cs.c = cs.c || GenLeft(a->down->right->right->right->right,1) ||
			"load returnvalue t0" ||
			"copy t1 t0 " + itostring(compute_size(a->down->right->right->right->right->tp)) ;
	}
  }   
  cs.c = cs.c || "retu" ; 

  if(maxoffsetauxspace > 0)
  {
	variable_data vd;
	vd.name = "aux_space";
	vd.size = maxoffsetauxspace ;
	cs.localvariables.push_back(vd);
  }
  
  symboltable.pop();
  l.push_back(cs);
  
  if(logable(DEBUG))
	cout<<"[CodeGenSubroutine] Ending with node \""<<a->kind<<"\""<< "at line " << a->line <<endl;

}

void CodeGen(AST *a,codeglobal &cg)
{
  initnumops();
  securemodeon();
  cg.mainsub.name="program";
  symboltable.push(a->sc);
  symboltable.setidtable("program");
  gencodevariablesandsetsizes(a->sc,cg.mainsub);
  for (AST *a1=child(child(a,1),0);a1!=0;a1=a1->right) {
    CodeGenSubroutine(a1,cg.l);
  }
  maxoffsetauxspace=0; newLabelIf(true); newLabelWhile(true);
  cg.mainsub.c=CodeGenInstruction(child(a,2))||"stop";
  if (maxoffsetauxspace>0) {
    variable_data vd;
    vd.name="aux_space";
    vd.size=maxoffsetauxspace;
    cg.mainsub.localvariables.push_back(vd);
  }
  symboltable.pop();
}

