package com.product.api.service;

import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.util.Base64;
import java.util.Date;
import java.util.List;

import com.product.api.dto.ApiResponse;
import com.product.api.entity.ProductImage;
import com.product.api.repository.RepoProductImage;
import com.product.exception.ApiException;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.context.annotation.PropertySource;
import org.springframework.http.HttpStatus;
import org.springframework.stereotype.Service;

@Service
@PropertySource("classpath:configuration/path.config")
public class SvcProductImageImp implements SvcProductImage {

    @Autowired
    RepoProductImage repo;

    @Value("${product.images.path}")
    private String path;

    @Override
    public List<ProductImage> getProductImages(Integer product_id) {
        return repo.findByProductId(product_id);
    }

    @Override
    public ApiResponse createProductImage(ProductImage in) {
        try {
            File folder = new File(path + "/" + in.getProduct_id());
            if (!folder.exists())
                folder.mkdirs();
            String file = path + in.getProduct_id() + "/img" + new Date().getTime() + ".bmp";
            // Decodificar imagen
            byte[] data = Base64.getMimeDecoder()
                    .decode(in.getImage().substring(in.getImage().indexOf(",") + 1, in.getImage().length()));
            try (OutputStream stream = new FileOutputStream(file)) {
                stream.write(data);
            }
            in.setStatus(1);
            in.setImage(file);
            repo.save(in);
            return new ApiResponse("product image created");
        } catch (Exception e) {
            throw new ApiException(HttpStatus.BAD_REQUEST, "product image cannot be created");
        }

    }

    @Override
    public ApiResponse deleteProductImage(Integer id) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public ApiResponse setProductImage(ProductImage in) {
        // TODO Auto-generated method stub
        return null;
    }
}
