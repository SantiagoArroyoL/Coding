package unam.ciencias.computoconcurrente;

import static org.junit.jupiter.api.Assertions.*;
import static unam.ciencias.computoconcurrente.PetersonTreeLockHelper.*;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

@EnabledIf("testSuiteEnabled")
class PetersonTreeLockHelperTest {

  static boolean testSuiteEnabled() {
    return PropertiesLoader.getBooleanProperty("tree-lock-helpers.enabled");
  }

  @Test
  void testGetLockID() {
    assertEquals(0, getCurrentLockIndex(8, 1, 0));
    assertEquals(1, getCurrentLockIndex(8, 1, 1));

    assertEquals(0, getCurrentLockIndex(8, 1, 2));
    assertEquals(1, getCurrentLockIndex(8, 1, 3));

    assertEquals(0, getCurrentLockIndex(8, 1, 4));
    assertEquals(1, getCurrentLockIndex(8, 1, 5));

    assertEquals(0, getCurrentLockIndex(8, 1, 6));
    assertEquals(1, getCurrentLockIndex(8, 1, 7));

    assertEquals(0, getCurrentLockIndex(8, 2, 0));
    assertEquals(0, getCurrentLockIndex(8, 2, 1));

    assertEquals(1, getCurrentLockIndex(8, 2, 2));
    assertEquals(1, getCurrentLockIndex(8, 2, 3));

    assertEquals(0, getCurrentLockIndex(8, 2, 4));
    assertEquals(0, getCurrentLockIndex(8, 2, 5));

    assertEquals(1, getCurrentLockIndex(8, 2, 6));
    assertEquals(1, getCurrentLockIndex(8, 2, 7));

    assertEquals(0, getCurrentLockIndex(8, 3, 0));
    assertEquals(0, getCurrentLockIndex(8, 3, 1));

    assertEquals(0, getCurrentLockIndex(8, 3, 2));
    assertEquals(0, getCurrentLockIndex(8, 3, 3));

    assertEquals(1, getCurrentLockIndex(8, 3, 4));
    assertEquals(1, getCurrentLockIndex(8, 3, 5));

    assertEquals(1, getCurrentLockIndex(8, 3, 6));
    assertEquals(1, getCurrentLockIndex(8, 3, 7));
  }

  @Test
  void testGetLockIndex() {
    assertEquals(4, getLockIndex(8, 1, 0));
    assertEquals(4, getLockIndex(8, 1, 1));

    assertEquals(5, getLockIndex(8, 1, 2));
    assertEquals(5, getLockIndex(8, 1, 3));

    assertEquals(6, getLockIndex(8, 1, 4));
    assertEquals(6, getLockIndex(8, 1, 5));

    assertEquals(7, getLockIndex(8, 1, 6));
    assertEquals(7, getLockIndex(8, 1, 7));

    assertEquals(2, getLockIndex(8, 2, 0));
    assertEquals(2, getLockIndex(8, 2, 1));

    assertEquals(2, getLockIndex(8, 2, 2));
    assertEquals(2, getLockIndex(8, 2, 3));

    assertEquals(3, getLockIndex(8, 2, 4));
    assertEquals(3, getLockIndex(8, 2, 5));

    assertEquals(3, getLockIndex(8, 2, 6));
    assertEquals(3, getLockIndex(8, 2, 7));

    assertEquals(1, getLockIndex(8, 3, 0));
    assertEquals(1, getLockIndex(8, 3, 1));

    assertEquals(1, getLockIndex(8, 3, 2));
    assertEquals(1, getLockIndex(8, 3, 3));

    assertEquals(1, getLockIndex(8, 3, 4));
    assertEquals(1, getLockIndex(8, 3, 5));

    assertEquals(1, getLockIndex(8, 3, 6));
    assertEquals(1, getLockIndex(8, 3, 7));
  }

  @Test
  void testGetLevelFromIndex() {
    assertEquals(3, getLevelFromIndex(8, 1));
    assertEquals(2, getLevelFromIndex(8, 2));
    assertEquals(2, getLevelFromIndex(8, 3));
    assertEquals(1, getLevelFromIndex(8, 4));
    assertEquals(1, getLevelFromIndex(8, 5));
    assertEquals(1, getLevelFromIndex(8, 6));
    assertEquals(1, getLevelFromIndex(8, 7));
  }

  @Test
  void testGetNeededLocks() {
    assertEquals(8, getNeededLocks(8));
    assertEquals(8, getNeededLocks(6));
    assertEquals(4, getNeededLocks(4));
    assertEquals(4, getNeededLocks(3));
    assertEquals(2, getNeededLocks(2));
  }
}
