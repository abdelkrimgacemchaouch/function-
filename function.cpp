#include "llvm/Pass.h"//
#include "llvm/IR/Function.h"//
#include "llvm/IR/Module.h"//
#include "llvm/Support/raw_ostream.h"//
#include "llvm/IR/Type.h"//
#include "llvm/IR/CallSite.h"//
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/Instructions.h"//
#include "llvm/IR/InstIterator.h"//
#include "llvm/IR/Constants.h"//
#include"Alloca.hpp"
#include"Load.hpp"
#include "BinairOperation.hpp"
#include "callop.hpp"
#include "Icmp.hpp"
#include "Store.hpp"
#include "search.hpp"
#include <iostream>
#include <fstream>
using namespace llvm;
using namespace std;
namespace {
  struct test : public ModulePass {
    static char ID;
    test() : ModulePass(ID) {}
   virtual  bool runOnModule(Module &M) {
    vector<Instruction*> orginal_alloca,copie_alloca,orginal_other_alloca,copie_other_alloca;//vector for alloca inst 
    vector<Instruction*> orginal_load,copie_load,orginal_other_load,copie_other_load; //vector for load inst
    vector<Instruction*> orginal_bin,copie_bin,orginal_other_bin,copie_other_bin;
    vector<Instruction*> orginal_icmp,copie_icmp;
    vector<Instruction*> orginal_other,copie_other;
    std::vector<Type*> P,m;
    std::vector<Function*> Funorg,Funclone;
    vector<Argument*> Aorg,Aclone;
    vector<BasicBlock*> BBorg,BBclone,X;
    vector<Instruction*> IBorg,IBclone;
    vector<Value*> l;
    vector<Instruction*> Iorg,Ireplace;
    LLVMContext &context = M.getContext();   
    for(Module::iterator f = M.begin(), fe = M.end(); f != fe; f++) 
      { 
      if(inst_begin(f)==inst_end(f))
       {
       errs()<<f->getName() <<"\n";
       }
      else 
        {
        Funorg.push_back(f);
        for (Function::arg_iterator I = f->arg_begin(), E = f->arg_end(); I != E; ++I)
          {
          if(I->getType()->isDoubleTy())
            {
            P.push_back(Type::getFloatTy(context));
            }
          else
            {
            P.push_back(I->getType());//take the type of the attribute of function orginal
            }
          Aorg.push_back(I);
          }
        }
      }
//********************************** creat the new function ****************************************
      FunctionType *FT;
      int a =0;
      for (int i=0;i<Funorg.size();i++)
        { 
        for (Function::const_arg_iterator I = Funorg[i]->arg_begin(), E = Funorg[i]->arg_end(); I != E; ++I)
          {
          m.push_back(P[a]); //take type of attribut of specific function
          a++;
          }
        FT = FunctionType::get(Funorg[i]->getFunctionType()->getReturnType(),m,false);
        Function* func = Function::Create(FT, Function::ExternalLinkage, "Foo", &M);
        Funclone.push_back(func); 
        m.clear();
        }
//************************************//take the type of the attribute of function clone************************
        for (int i=0;i<Funclone.size();i++)
         {
         for (Function::arg_iterator I = Funclone[i]->arg_begin(), E = Funclone[i]->arg_end(); I != E; ++I)
          {
          Aclone.push_back(I);
          }
         }
//*****************************************************************************************************************

//**********************************copy the instruction to the clone functuion****************************************
      int n2;
      for (int i=0;i<Funorg.size();i++)
        {
        for (Function::iterator blocdebase = Funorg[i]->begin(), e = Funorg[i]->end(); blocdebase != e; ++blocdebase)
          {
          BBorg.push_back(blocdebase);
          BasicBlock *BB = BasicBlock::Create(context, "EntryBlock", Funclone[i]);
          for (BasicBlock::iterator instruction = blocdebase->begin(), ee = blocdebase->end(); instruction != ee; ++instruction)
            {
            //*************************allocainst*********************************************************
            if(dyn_cast<AllocaInst>(instruction))
              {
              aloca(instruction,BB,orginal_alloca,copie_alloca,orginal_other_alloca,copie_other_alloca);
              }
              //***********************************storeinst********************************************
            else if (StoreInst *store = dyn_cast<StoreInst>(instruction))
              {
              //errs()<<*store->getOperand(1)<<"  \n";errs()<<orginal_alloca.size()<<"\n";
              if(dyn_cast<Argument>(store->getOperand(0)))
                {
                int n = Searcharg(Aorg,dyn_cast<Argument>(instruction->getOperand(0)));
                n2= Searchinst(orginal_alloca,dyn_cast<Instruction>(instruction->getOperand(1)));
                if(n2<orginal_alloca.size())
                  {
                  //errs()<<*instruction->getOperand(1) <<" "<< n2<<"\n";
                  StoreInst* new_store = new StoreInst(Aclone[n],copie_alloca[n2] , false,4);
                  BB->getInstList().push_back(new_store);
                  }
                //errs() <<*orginal_alloca[n2]<<" "<<*copie_alloca[n2]<<"\n";
               /* errs()<<*store<<"\n";
                Instruction *II= instruction->clone();
                BB->getInstList().push_back(II);
                for (Function::const_arg_iterator I = Funorg[i]->arg_begin(), E = Funorg[i]->arg_end(); I != E; ++I)
                   {
                    //n2=Searchinst(Aorg,dyn_cast<Instruction>(instruction->getOperand(0)));
                    n2=Searcharg(Aorg,cast<Argument>(store->getOperand(0)));
                    II->setOperand(0,Aclone[n2]);
                    n2=Searchinst(orginal_alloca,dyn_cast<Instruction>(instruction->getOperand(1)));
                    if(n2<orginal_alloca.size())
                      {
                      errs()<<n2<<" "<<*instruction <<"\n";
                      //II->setOperand(1,copie_alloca[n2]);
                      }
                   }*/
                }
              else 
              {  
              if(dyn_cast<GetElementPtrInst>(store->getOperand(1)))
                {
               // store_gep(instruction,BB,orginal_other,orginal_GEP,copie_other,copie_GEP);
                }
              else
                {
                if (store->getOperand(0)->getType()->isDoubleTy())
                  {
                  store_var_double(instruction,BB,orginal_bin,orginal_alloca,copie_bin,copie_alloca);                  
                  }
                else
                  {
                  store_var_other(instruction,BB,orginal_other_bin,orginal_other_alloca,copie_other_bin,copie_other_alloca);
                  }
                }     
              }
              }
              //*************************************load inst******************************************
              else if (LoadInst *load = dyn_cast<LoadInst>(instruction))
              {
              if (load->getType()->isDoubleTy())
                  {
                  //errs()<<*load->getOperand(0) <<" \n";
                  load_aloca_doubles(instruction,BB,orginal_alloca,copie_alloca,orginal_load,copie_load);
                  }
                else
                  {
                  load_aloca_other(instruction,BB,orginal_other_alloca,copie_other_alloca,orginal_other_load,copie_other_load);
                  }      
              }
              //******************************binary inst *******************************************
              else if (BinaryOperator* binOp = dyn_cast<BinaryOperator>(instruction))
              {
               if (binOp->getType()->isDoubleTy())
                {
                if(dyn_cast<LoadInst>(binOp->getOperand(0))&&dyn_cast<LoadInst>(binOp->getOperand(1)))
		               {
		               binop_2load_doubles(instruction,BB,orginal_bin,orginal_load,copie_load,copie_bin);
		               } 
		            else
		               {
		               if((dyn_cast<LoadInst>(binOp->getOperand(1))&&dyn_cast<ConstantFP>(binOp->getOperand(0))) || (dyn_cast<LoadInst>(binOp->getOperand(0))&&dyn_cast<ConstantFP>(binOp->getOperand(1))) )
		                  {
		                  binop_load_const_double(instruction,BB,orginal_bin,orginal_load,copie_load,copie_bin);
		                  }    
		               } 
		           }//if doublty 
		           else    //not Double binary operation
                {
                 if(dyn_cast<LoadInst>(binOp->getOperand(0))&&dyn_cast<LoadInst>(binOp->getOperand(1)))
		              {
		              binop_2load_notdoubles(instruction,BB,orginal_other_bin,orginal_other_load,copie_other_load,copie_other_bin);
		              }
                 else if((dyn_cast<LoadInst>(binOp->getOperand(0)) &&dyn_cast<ConstantInt>(binOp->getOperand(1)))||(dyn_cast<LoadInst>(binOp->getOperand(1)) &&dyn_cast<ConstantInt>(binOp->getOperand(0))))
                  {
                  binop_load_const_notdouble(instruction,BB,orginal_other_bin,orginal_other_load,copie_other_load,copie_other_bin);
                  } 
                 else
                  {
                  if((dyn_cast<LoadInst>(binOp->getOperand(0))) || (dyn_cast<LoadInst>(binOp->getOperand(1))))
                    {
                   // binop_1load_notdouble(instruction,BB,orginal_other_bin,orginal_other_load,orginal_other,copie_other_load,copie_other,copie_other_bin);
                    }                     
                  } 
                }	       
             }
             //*********************************************callinst*********************************
             else if(CallInst *call=dyn_cast<CallInst>(instruction))
              {
              if(dyn_cast<LoadInst>(call->getOperand(0))&&dyn_cast<LoadInst>(call->getOperand(1)))
                {
                call_2_load(instruction,BB,orginal_load,copie_load,orginal_other,copie_other);  
                }
              else if (dyn_cast<LoadInst>(call->getOperand(1)))  
                {
                call_1_load(instruction,BB,orginal_load,copie_load,orginal_other_load,copie_other_load);  
                }
              else if(dyn_cast<AllocaInst>(call->getOperand(1)) )
                {
                call_aloca(instruction,BB,orginal_alloca,copie_alloca,orginal_other_alloca,copie_other_alloca); 
                }
              else if(dyn_cast<GetElementPtrInst>(call->getOperand(1)))
                {
               // call_GEP(instruction,BB,orginal_GEP,copie_GEP,orginal_other_GEP,copie_other_GEP);
                }      
              }
              //********************************************icmpinst*********************************
              else if(ICmpInst *icmp=dyn_cast<ICmpInst>(instruction))
              {            
                if(dyn_cast<LoadInst>(icmp->getOperand(0))&&dyn_cast<LoadInst>(icmp->getOperand(1)))
                  {
                  icmp_2load(instruction,BB,orginal_icmp,orginal_other_load,copie_other_load,copie_icmp);
                  }
                else
                  {
                  icmp_1load(instruction,BB,orginal_icmp,orginal_other_load,copie_other_load,copie_icmp);      
                  }                  
              }
              //******************************************************************
              
              //**************************************otherinst**************************************
            else 
              {
              Instruction *I= instruction->clone();
              BB->getInstList().push_back(I);
              IBorg.push_back(instruction);
              IBclone.push_back(I);
              }  
            }
          BBclone.push_back(BB);
          }    
        for(int i=0;i<(BBorg.size());i++)
          {
          if (BranchInst *CI = dyn_cast<BranchInst>(BBclone[i]->getTerminator ()))
            {
            if(CI->isConditional())
              {
              int index= Search(BBorg,CI->getSuccessor(0));
              int  index1= Search(BBorg,CI->getSuccessor(1)); 
              int n=Searchinst(orginal_icmp,dyn_cast<Instruction>(CI->getCondition()));
              BranchInst::Create (BBclone[index],BBclone[index1] ,copie_icmp[n],BBclone[i]);
              }
            else
              {
              int index= Search(BBorg,CI->getSuccessor(0));
              BranchInst::Create(BBclone[index],BBclone[i]);
              }
          CI->eraseFromParent();    
            }  
          }
          if (ReturnInst *ret=dyn_cast<ReturnInst>(BBclone[i]->getTerminator ()))
            {
            Type* doublety= Type::getDoubleTy(context);
            if (dyn_cast<BinaryOperator>(ret->getOperand(0)))
              {
              int n=Searchinst(orginal_bin,dyn_cast<Instruction>(ret->getOperand(0)));
              FPExtInst *c= new FPExtInst  (copie_bin[n], doublety, "");
              c->insertAfter(copie_bin[n]);
              ret->setOperand(0,c);
              }
                
            }
            
        BBclone.clear();
        BBorg.clear();
        }
//*******************************************************************************************************        
for(int i=0;i<Funclone.size();i++) 
  {
  for (Function::iterator blocdebase = Funclone[i]->begin(), e = Funclone[i]->end(); blocdebase != e; ++blocdebase)
    {    
    for (BasicBlock::iterator instruction = blocdebase->begin(), ee = blocdebase->end(); instruction != ee; ++instruction)
     {
      int n=Searchinst(orginal_other,dyn_cast<Instruction>(instruction->getOperand(0)));
      if(n<orginal_other.size())
        {
        instruction->setOperand(0,copie_other[n]);
        }
     }
    }
        
  }
  //**********************************************************************************************************
//*****************************************for orginal function********************************************************       
Type* type = Type::getFloatTy(context);
Value *One = ConstantInt::get(Type::getInt32Ty(context), 0);
    Value *Two = ConstantInt::get(Type::getInt32Ty(context), 1);
for (int i=0;i<Funorg.size();i++)
  {
  if(inst_begin(Funorg[i])==inst_end(Funorg[i]))
    {
    errs()<<"...............;\n";
    }
  else 
    {
    for (Function::iterator blocdebase = Funorg[i]->begin(), e = Funorg[i]->end(); blocdebase != e; ++blocdebase)
      {      
      if(pred_begin(blocdebase)==pred_end(blocdebase))
        {
        blocdebase->setName(Funorg[i]->getName());
        X.push_back(blocdebase);     
        }  
      }
    FPTruncInst *c;  
    BasicBlock * BB = BasicBlock::Create(context, "blocdechoix",Funorg[i] ,Funorg[i]->begin());
    for (Function::arg_iterator I = Funorg[i]->arg_begin(), E = Funorg[i]->arg_end(); I != E; ++I)
          {
          if (I->getType()->isDoubleTy())
            {
            c= new FPTruncInst  (I, type, "conv",BB);
            l.push_back(c);
            }
          else 
            {
            l.push_back(I);
            }
          } 
    BasicBlock * B = BasicBlock::Create(context, "entrybloc",Funorg[i],Funorg[i]->begin());
    BranchInst::Create(BB,B);
    BasicBlock * BB1 = BasicBlock::Create(context, "blocother",Funorg[i]);
    Value *CondInst = new ICmpInst(*BB, ICmpInst::ICMP_SLE, One, Two, "cond");
    BranchInst::Create(BB1,X[0],CondInst,BB);   
    CallInst *O= CallInst::Create(Funclone[i], l, "",BB1);
    Type* ty = Funclone[i]->getReturnType();
    AllocaInst *new_alloca = new AllocaInst(ty,0, 4, "a",BB1);
    StoreInst  *new_store = new StoreInst(O,new_alloca , false,4,BB1);
    LoadInst  *new_load = new LoadInst(new_alloca," ",false,4,BB1);
    ReturnInst::Create(context, new_load, BB1);
    X.clear();
    l.clear();
    } 
  }
//**************************************for function clone********************************************
Type* typeD = Type::getDoubleTy(context);
for (int i=0;i<Funclone.size();i++)
  {
  if(inst_begin(Funclone[i])==inst_end(Funclone[i]))
    {
    errs()<<"...............;\n";
    }
  else 
    {
    for (Function::iterator blocdebase = Funclone[i]->begin(), e = Funclone[i]->end(); blocdebase != e; ++blocdebase)
      {      
      if(pred_begin(blocdebase)==pred_end(blocdebase))
        {
        blocdebase->setName(Funclone[i]->getName());
        X.push_back(blocdebase);     
        }  
      }
    FPExtInst *c;
    BasicBlock * BB = BasicBlock::Create(context, "blocdechoix",Funclone[i] ,Funclone[i]->begin());
    for (Function::arg_iterator I = Funclone[i]->arg_begin(), E = Funclone[i]->arg_end(); I != E; ++I)
      {
      if (I->getType()->isFloatTy())
        {
        c= new FPExtInst  (I, typeD, "convD",BB);
        l.push_back(c);
        }
      else 
        {
        l.push_back(I);
        }
      }
    BasicBlock * B = BasicBlock::Create(context, "entrybloc",Funclone[i],Funclone[i]->begin());    
    BranchInst::Create(BB,B);
    BasicBlock * BB1 = BasicBlock::Create(context, "blocother",Funclone[i]);
    One = ConstantInt::get(Type::getInt32Ty(context), 1);
    Two = ConstantInt::get(Type::getInt32Ty(context), 0);
    Value *CondInst = new ICmpInst(*BB, ICmpInst::ICMP_SLE, One, Two, "cond");
    BranchInst::Create(BB1,X[0],CondInst,BB);   
    CallInst *O= CallInst::Create(Funorg[i], l, "",BB1);
    Type* ty = Funorg[i]->getReturnType();
    AllocaInst *new_alloca = new AllocaInst(ty,0, 8, "a",BB1);
    StoreInst  *new_store = new StoreInst(O,new_alloca , false,8,BB1);
    LoadInst  *new_load = new LoadInst(new_alloca," ",false,8,BB1);
    ReturnInst::Create(context, new_load, BB1);
    X.clear();
    l.clear();
    //One = ConstantInt::get(Type::getInt32Ty(context), 1);
    //Two = ConstantInt::get(Type::getInt32Ty(context), 0);
    }  
  }
//*****************************************************************************************************
for(Module::iterator f = M.begin(), fe = M.end(); f != fe; f++) {

for (Function::iterator blocdebase = f->begin(), e = f->end(); blocdebase != e; ++blocdebase){
errs()<<*blocdebase<<":"<<"\n";
}
}

/*
//**********************************repair the instruction cloned ***********************************************
        int n2;
        for (int i=0;i<Funclone.size();i++)
          {
          for (Function::iterator blocdebase = Funclone[i]->begin(), e = Funclone[i]->end(); blocdebase != e; ++blocdebase)
            {    
              for (BasicBlock::iterator instruction = blocdebase->begin(), ee = blocdebase->end(); instruction != ee; ++instruction)
                {
                //************************for the attribut of each function*****************************************************
                  for (Function::const_arg_iterator I = Funorg[i]->arg_begin(), E = Funorg[i]->arg_end(); I != E; ++I)
                   {
                   if(I==instruction->getOperand(0))
                    {
                    n2=Searchinst(IBclone,dyn_cast<Instruction>(instruction));
                    n2=Searcharg(Aorg,cast<Argument>(IBorg[n2]->getOperand(0)));
                    instruction->setOperand(0,Aclone[n2]);
                    }
                   }
                 //*************************************************************************************************************
                if (instruction->getNumOperands ()==1)
                  {
                  int n =Searchinst(IBorg,dyn_cast<Instruction>(instruction->getOperand(0)));
                  if (n<=IBorg.size())
                    {  
                    instruction->setOperand (0,IBclone[n]);
                    } 
                  }
                else if(instruction->getNumOperands ()>1)
                  {
                  int n1 =Searchinst(IBorg,dyn_cast<Instruction>(instruction->getOperand(1)));
                  int n =Searchinst(IBorg,dyn_cast<Instruction>(instruction->getOperand(0)));
                  if (n1<=IBorg.size())
                    {
                    instruction->setOperand (1,IBclone[n1]);
                    }
                  if (n<=IBorg.size())
                    {
                    instruction->setOperand (0,IBclone[n]);
                    }
                  }   
                }
            }
          }
//****************************************convertion ************************************************
Type* type = Type::getFloatTy(context);
Type* doublety= Type::getDoubleTy(context);
for (int i=0;i<Funclone.size();i++)
          {
          for (Function::iterator blocdebase = Funclone[i]->begin(), e = Funclone[i]->end(); blocdebase != e; ++blocdebase)
            {
              for (BasicBlock::iterator instruction = blocdebase->begin(), ee = blocdebase->end(); instruction != ee; ++instruction)
                {
                if(!(instruction->mayReadFromMemory ())&& !(instruction->mayWriteToMemory())&&(instruction->getType()->isDoubleTy()))
                  {
                  if (BinaryOperator *binop= dyn_cast<BinaryOperator>(instruction))
                    {
                    Iorg.push_back(instruction);
                    FPTruncInst *c= new FPTruncInst  (instruction->getOperand(0), type, "conv",instruction);
                    FPTruncInst *c1= new FPTruncInst  (instruction->getOperand(1), type, "conv",instruction);
                    BinaryOperator *binOpcopie = BinaryOperator::Create(binop->getOpcode(),c,c1,"add",instruction);
                    Ireplace.push_back(binOpcopie);
                    }
                  }
                if (instruction->mayWriteToMemory())
                  {
                  int n =Searchinst(Iorg,dyn_cast<Instruction>(instruction->getOperand(0)));
                  if(n<Iorg.size())
                    {
                    FPExtInst *c= new FPExtInst  (Ireplace[n], doublety, "",instruction);
                    instruction->setOperand(0,c);
                    Iorg[n]->eraseFromParent();
                    }                 
                  } 
                }
            }
            
           }             
//**********************************************************************************************************************************
int j;
for (int i=0;i<Funorg.size();i++)
  {
  if(inst_begin(Funorg[i])==inst_end(Funorg[i]))
    {
    errs()<<"...............;\n";
    }
  else 
    {
    for (Function::iterator blocdebase = Funorg[i]->begin(), e = Funorg[i]->end(); blocdebase != e; ++blocdebase)
      {      
      if(pred_begin(blocdebase)==pred_end(blocdebase))
        {
        blocdebase->setName(Funorg[i]->getName());
        X.push_back(blocdebase);     
        }
  
      }
    BasicBlock * BB = BasicBlock::Create(context, "blocdechoix",Funorg[i] ,Funorg[i]->begin());
    for (Function::arg_iterator I = Funorg[i]->arg_begin(), E = Funorg[i]->arg_end(); I != E; ++I)
          {
          l.push_back(I);
          } 
    BasicBlock * B = BasicBlock::Create(context, "entrybloc",Funorg[i],Funorg[i]->begin());
    BranchInst::Create(BB,B);
    BasicBlock * BB1 = BasicBlock::Create(context, "blocother",Funorg[i]);
    Value *One = ConstantInt::get(Type::getInt32Ty(context), 1);
    Value *Two = ConstantInt::get(Type::getInt32Ty(context), 0);
    Value *CondInst = new ICmpInst(*BB, ICmpInst::ICMP_SLE, One, Two, "cond");
    BranchInst::Create(X[0],BB1,CondInst,BB);   
    CallInst::Create(Funclone[i], l, "",BB1);
    BranchInst::Create(BB,BB1);
    X.clear();
    l.clear();
    } 
  }

//***********************************************************************************************************************************
for (int i=0;i<Funclone.size();i++)
          {
          for (Function::iterator blocdebase = Funclone[i]->begin(), e = Funclone[i]->end(); blocdebase != e; ++blocdebase)
            {
              for (BasicBlock::iterator instruction = blocdebase->begin(), ee = blocdebase->end(); instruction != ee; ++instruction)
                {
                
                if(dyn_cast<CallInst>(instruction))
                  {
                  //errs()<<*instruction<<"\n";
                  }
                }
            }
          }     
//************************************************************************************************************************************
/*for(Module::iterator f = M.begin(), fe = M.end(); f != fe; f++) {
errs()<<f->getName()<<":\n";
if(inst_begin(f)==inst_end(f)){errs()<<"fonction n'a pas d'instructions\n";}
else {
for (inst_iterator I = inst_begin(f), E = inst_end(f); I != E; ++I)
  {
  errs() << *I << "\n";
}
}
}*/
//********************************************************************************************************
for(Module::iterator f = M.begin(), fe = M.end(); f != fe; f++) {
//errs()<<*f->getType()<<"::  "<<f->getName()<<":"<<"\n";
for (Function::iterator blocdebase = f->begin(), e = f->end(); blocdebase != e; ++blocdebase){
}
}
return true;//false si on veut pas de changement
}
  };
}
char test::ID = 0;
static RegisterPass<test> X("Test", "Hello World Pass", false, false);

