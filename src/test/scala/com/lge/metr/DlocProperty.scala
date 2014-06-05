package com.lge.metr

import org.scalacheck.Properties
import org.scalacheck.Prop.forAll
import org.scalacheck.Prop.BooleanOperators
import org.scalacheck.Arbitrary._
import org.scalacheck._
import Gen._
import scala.language.implicitConversions

import JavaModel._

object DlocProperty extends Properties("Metr") with MetricCounter {
  def genIf(sz:Int): Gen[Stmt] = 
    for {
      thenPart <- genStmt(sz/2)
      elseStmts <- genStmt(sz/2)
      elsePart <- oneOf(None, Some(elseStmts))
    } yield IfStmt(thenPart, elsePart)

  def genSwitch(sz:Int): Gen[Stmt] = for {
    n <- choose(sz/3, sz/2)
    cases <- listOfN(n, genStmt(sz/2))
  } yield SwitchStmt(cases)

  def genLoop(sz:Int): Gen[Stmt] = for {
    body <- genStmt(sz/2)
  } yield LoopStmt("keyword", body)

  def genBlock(sz:Int): Gen[Stmt] = for {
    n <- choose(sz/3, sz/2)
    statements <- listOfN(n, genStmt(sz/2))
  } yield BlockStmt(statements)

  def genSync(sz:Int): Gen[Stmt] = for {
    body <- genStmt(sz/2)
  } yield SyncStmt(body)

  def genTry(sz:Int): Gen[Stmt] = for {
    body <- genStmt(sz/2)
    catchers <- listOfN(sz/2, genStmt(sz/2))
    stmt <- genStmt(sz/2)
    finalizer <- oneOf(None, Some(stmt))
  } yield TryStmt(body, catchers, finalizer)
    
  def genStmt(sz:Int): Gen[Stmt] = {
    if (sz <= 0) const(OtherStmt())
    else
      frequency((3, genIf(sz/2)),    (3, genSwitch(sz/2)), (3, genLoop(sz/2)), 
                (3, genBlock(sz/2)), (3, genSync(sz/2)),   (3, genTry(sz/2)),
                (1, const(OtherStmt())))
  }

  def genMethod(sz:Int): Gen[Method] = for {
    body <- genStmt(sz/2)
  } yield Method("method", body)

  def genCtor(sz:Int): Gen[Ctor] = for {
    body <- genStmt(sz/2)
  } yield Ctor("ctor", body)

  implicit def arbExecutable: Arbitrary[Executable] = Arbitrary {

    def sizedExecutable(sz:Int): Gen[Executable] = 
      oneOf(genMethod(sz/2), genCtor(sz/2))

    sized(sz => sizedExecutable(sz))
  }

  implicit def arbStmt: Arbitrary[Stmt] = Arbitrary {
    sized(sz => genStmt(sz))
  }

  implicit def stmtToExecutable(stmt:Stmt): Executable = {
    Method("stmt2Method", stmt)
  }

  def codefat(exe:Executable): Double = (sloc(exe) - dloc(exe)) / sloc(exe)
  def isSlocZero(exe:Executable): Boolean = sloc(exe) == 0

  // "모든 메소드에 대해 SLOC >= DLOC 이다. "
  property(" #1. 모든 메소드에 대해 SLOC >= DLOC 이다.(invariant)") = forAll {(exe:Executable) => 
    sloc(exe) >= dloc(exe)
  }

  // "CodeFat: control flow 상의 decision depth 를 증가시키는 요소들(if/switch-case/while/for/do-while)을 
  // 코드상의 지방 요소라고 보아, 전체 코드에서 얼마나 지방 요소가 포함되어 있는지 비율로 나타낸 지표"
  property(" #2. 임의의 statement 에 대해 if 로 감싸면 codefat 이 증가한다.") = forAll {(stmt:Stmt) => 
    val stmtIfNested = IfStmt(stmt, None)

    !isSlocZero(stmt) ==> codefat(stmtIfNested) > codefat(stmt)
  }

  property(" #3. codefat 은 IF 문이 블락 끝에 추가되는 것 보다 중첩될 때 더 증가한다.") = 
  forAll {(stmt:Stmt) => 
    val ifNested = IfStmt(stmt,None)
    val ifAppended = BlockStmt(List(stmt, IfStmt(BlockStmt(List()), None)))
  
    !isSlocZero(stmt) ==> codefat(ifNested) > codefat(ifAppended)
  }

  property(" #4. dloc 는 Block 문에 대해 분배법칙이 성립한다.") =
  forAll {(stmt1:Stmt, stmt2:Stmt) => {

    dloc(stmt1) + dloc(stmt2) == dloc(BlockStmt(List(stmt1, stmt2)))

  }}
}


