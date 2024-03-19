package unam.ciencias.computoconcurrente;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import org.junit.jupiter.api.condition.EnabledIf;

@Target(ElementType.METHOD)
@Retention(RetentionPolicy.RUNTIME)
@EnabledIf("hasNotDefaultCores")
public @interface EnableIfHasNotDefaultCores {}
