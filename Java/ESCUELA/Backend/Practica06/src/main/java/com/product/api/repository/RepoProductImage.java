package com.product.api.repository;

import java.util.List;

import javax.transaction.Transactional;

import com.product.api.entity.ProductImage;

import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;
import org.springframework.stereotype.Repository;

@Repository
public interface RepoProductImage extends JpaRepository<ProductImage, Integer> {

    @Query(value = "SLECT * FROM product_image WHERE product_id =:product_id AND status = 1", nativeQuery = true)
    List<ProductImage> findByProductId(@Param("product_id") Integer product_id);

    @Modifying
    @Transactional
    @Query(value = "UPDATE product_image SET status = 0 WHERE product_image_id = :product_image_id AND status = 1", nativeQuery = true)
    Integer deleteProductImage(@Param("product_image_id") Integer product_image_id);
}
