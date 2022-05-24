package com.product.api.repository;

import java.util.List;

import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;
import org.springframework.stereotype.Repository;
import org.springframework.transaction.annotation.Transactional;

import com.product.api.entity.Product;

@Repository
public interface RepoProduct extends JpaRepository<Product, Integer> {

        List<Product> findByStatus(Integer status); // Hibernate

        Product findByGtinAndStatus(@Param("gtin") String gtin, @Param("status") Integer status);

        @Modifying
        @Transactional
        @Query(value = "UPDATE costumer "
                        + "SET gtin = :gtin, "
                        + "product = :product, "
                        + "description = :description, "
                        + "price = :price, "
                        + "stock = :stock, "
                        + "WHERE product_id = :product_id AND status = 1", nativeQuery = true)
        Integer updateProduct(@Param("product_id") int product_id,
                        @Param("gtin") String gtin,
                        @Param("product") String product,
                        @Param("description") String description,
                        @Param("price") Double price,
                        @Param("stock") int stock);

        @Modifying
        @Transactional
        @Query(value = "UPDATE product SET status = 0 WHERE product_id = :product_id AND status = 1", nativeQuery = true)
        Integer deleteProduct(@Param("product_id") int product_id);

        @Modifying
        @Transactional
        @Query(value = "UPDATE product SET category_id = :category_id WHERE product_id = :product_id AND status = 1", nativeQuery = true)
        Integer updateProductCategory(@Param("category_id") Integer category_id,
                        @Param("product_id") Integer product_id);
}
