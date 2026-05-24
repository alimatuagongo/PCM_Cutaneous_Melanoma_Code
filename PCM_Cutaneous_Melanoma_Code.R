t<-proc.time()
# Needed libraries
library(survival)
library(survminer)
library(MASS)
library(e1071)
library(pROC)
library(caTools)
library(caret)
library(rpart)
library(neuralnet)
library(randomForest)
library(randomForestSRC)
library(xgboost)
library(splines)
library(readr)
library(timeROC)

# --- Function: smsurv (Weighted Breslow Estimator) ---
smsurv <- function(Time, Status, X, beta, w, model) {
  death_point <- sort(unique(subset(Time, Status == 1)))
  
  if (length(death_point) == 0) {
    return(list(survival = rep(1, length(Time)), death_times = NULL, s0_vals = NULL))
  }
  
  if(is.null(beta) || length(beta) < (ncol(X) - 1)) {
    beta <- c(beta, rep(0, (ncol(X) - 1) - length(beta)))
  }
  
  .eps <- 1e-10
  
  if (model == 'ph') {
    coxexp <- exp(X[, -1, drop = FALSE] %*% beta)
  }
  
  lambda <- numeric(length(death_point))
  event <- numeric(length(death_point))
  
  for (i in 1:length(death_point)) {
    event[i] <- sum(Status * as.numeric(Time == death_point[i]))
    if (model == 'ph') temp <- sum(as.numeric(Time >= death_point[i]) * w * drop(coxexp))
    if (model == 'aft') temp <- sum(as.numeric(Time >= death_point[i]) * w)
    
    if (!is.na(temp) && temp > .eps) {
      lambda[i] <- event[i] / temp
    } else {
      lambda[i] <- 0
    }
  }
  
  s0_at_deaths <- exp(-cumsum(lambda))
  
  survival <- sapply(Time, function(t) {
    if (t < min(death_point)) return(1)
    s0_at_deaths[max(which(death_point <= t))]
  })
  
  survival <- pmin(pmax(survival, .eps), 1 - .eps)
  
  return(list(survival = survival, death_times = death_point, s0_vals = s0_at_deaths))
}



# Logit 
em.Logit.Pois <- function(Time, Status, Time1, Status1,
                          X, X1, Z, Z1,
                          b, beta, s0, s01,
                          emmax, eps) {
  
  n <- length(Status)
  s  <- s0
  s1 <- s01
  
  convergence <- 1000
  i <- 1
  
  while (convergence > eps && i <= emmax) {
    UN <- matrix(exp(Z %*% b)/(1+exp(Z %*% b)),ncol=1)
    PRED <- matrix(exp(Z1 %*% b)/(1+exp(Z1 %*% b)),ncol=1)
    
    
    survival  <- drop(s^(exp(X[, -1, drop=FALSE] %*% beta)))
    survival1 <- drop(s1^(exp(X1[, -1, drop=FALSE] %*% beta)))
    
    # E-STEP: Using matched probabilities for Train (UN) and Test (PRED)
    M <- Status - (survival * log(pmax(1 - UN, 1e-6)))
    M1 <- Status1 - (survival1 * log(pmax(1 - PRED, 1e-6)))
    
    # Incidence Part (M-STEP)
    Q1 <- function(par) {
      bb <- par
      u_temp <- matrix(exp(Z %*% bb)/(1+exp(Z %*% bb)),ncol=1)
      loglik <- sum(M*log(-log(pmax(1-u_temp, 1e-10)))) + sum(log(pmax(1-u_temp, 1e-10)))
      return(-loglik)
    }
    
    update_b = optim(par=b,fn=Q1,method="Nelder-Mead")$par 
    
    # Latency Part (M-STEP)
    fit_w <- coxph(Surv(Time, Status) ~ X[, -1, drop = FALSE] + offset(log(pmax(M, 1e-4))),
                   subset = M != 0, method = "breslow")
    update_beta <- fit_w$coef
    
    update_s <- smsurv(Time, Status, X, update_beta, w = M, model = "ph")$survival
    update_s1 <- smsurv(Time1, Status1, X1, update_beta, w = M1, model = "ph")$survival
    
    convergence <- sum((update_b - b)^2) + sum((update_beta - beta)^2)
    
    b <- update_b
    beta <- update_beta 
    s <- update_s
    s1 <- update_s1
    
    i <- i+1
  }
  
  # Final calculation for returns
  UN <- matrix(exp(Z %*% b)/(1+exp(Z %*% b)),ncol=1)
  PRED <- matrix(exp(Z1 %*% b)/(1+exp(Z1 %*% b)),ncol=1)
  survival  <- drop(s^(exp(X[, -1, drop=FALSE] %*% beta)))
  survival1 <- drop(s1^(exp(X1[, -1, drop=FALSE] %*% beta)))
  Sp <- (1 - UN)^(1 - survival)
  Sp.pred <- (1 - PRED)^(1 - survival1)
  S1 = (Sp-(1-UN))/UN 
  S1.pred = (Sp.pred-(1-PRED))/PRED
  
  return(list(
    b = b,
    latencyfit = beta,
    UN = UN,
    PRED = PRED,
    Sp = Sp,
    Sp.pred = Sp.pred,
    S1 = S1,
    S1.pred = S1.pred,
    s0 = s,
    s01 = s1,
    S = survival,
    S.pred = survival1,
    tau = convergence
  ))
}

smcure.Logit.Pois <- function(train, test,  Var = F, emmax = 1000, eps = 1e-3, nboot = 100){
  
  Time <- train$t; Status <- train$d
  Time1 <- test$t; Status1 <- test$d
  
  X <- model.matrix(~ x2 + x3 + x4 + x6, data = train)
  X1 <- model.matrix(~ x2 + x3 + x4 + x6, data = test)
  Z <- model.matrix(~ x2 + x3 + x4 + x6, data = train)
  Z1 <- model.matrix(~ x2 + x3 + x4 + x6, data = test)
  
  #Scaling age and tumor thickness
  cols_scale <- colnames(X) %in% c("x2", "x6")
  scale_params <- list(
    x2 = list(mean = mean(X[, "x2"]), sd = sd(X[, "x2"])),
    x6 = list(mean = mean(X[, "x6"]), sd = sd(X[, "x6"]))
  )
  X[, cols_scale] <- scale(X[, cols_scale])
  X1[, "x2"] <- (X1[, "x2"] - scale_params$x2$mean) / scale_params$x2$sd
  X1[, "x6"] <- (X1[, "x6"] - scale_params$x6$mean) / scale_params$x6$sd
  
  Z <- X; Z1 <- X1
  
  
  
  coxfit_train <- coxph(Surv(Time, Status) ~ 1, data = train)
  coxfit_test <- coxph(Surv(Time1, Status1) ~ 1, data = test)
  
  out.data <- basehaz(coxfit_train, centered = FALSE)  # columns: hazard, time
  out.data1 <- basehaz( coxfit_test, centered = FALSE)  # columns: hazard, time
  t_grid  <- out.data$time
  t_grid1  <- out.data1$time
  idx_tr <- pmax(1, findInterval(Time,  t_grid))
  idx_te <- pmax(1, findInterval(Time1, t_grid1))
  S0_grid <- exp(-out.data$hazard)
  S01_grid <- exp(-out.data1$hazard)
  
  
  # initial full versions
  s0_full  <- exp(-out.data[,1])
  s01_full <- exp(-out.data1[,1])
  
  
  
  s0_init  <- S0_grid # length(Time)
  s01_init <- S01_grid  # length(Time1)
  
  
  
  
  
  
  if(any(is.na(s0_init))) s0_init[is.na(s0_init)] <- min(s0_init, na.rm = TRUE)
  if(any(is.na(s01_init))) s01_init[is.na(s01_init)] <- min(s01_init, na.rm = TRUE)
  
  
  b_start <- rep(0, ncol(Z))
  
  
  beta_start <- coxfit_train$coefficients
  if (is.null(beta_start) || length(beta_start) != (ncol(X) - 1)) {
    beta_start <- rep(0, ncol(X) - 1)
  } else {
    beta_start <- as.numeric(beta_start)
  }
  
  
  emfit <- em.Logit.Pois(Time, Status, Time1, Status1,
                         X, X1, Z, Z1,
                         b_start, beta_start, s0_init, s01_init,
                         emmax, eps) 
  b.est <- emfit$b
  beta.est <- emfit$latencyfit
  
  if (Var) {
    n_latency <- length(beta.est)
    n_incidence <- length(b.est)
    
    latency_boot <- matrix(NA_real_, nrow = nboot, ncol = n_latency)
    incidence_boot <- matrix(NA_real_, nrow = nboot, ncol = n_incidence)
    
    cat("Starting bootstrap (", nboot, " iterations)...\n")
    
    for (i in 1:nboot) {
      cat("Bootstrap", i, "of", nboot, "\n")
      boot_idx <- sample(seq_along(Status), length(Status), replace = TRUE)
      
      Time_b   <- Time[boot_idx]
      Status_b <- Status[boot_idx]
      X_b      <- X[boot_idx, , drop = FALSE]
      Z_b      <- Z[boot_idx, , drop = FALSE]
      
      boot_train_df <- data.frame(
        t  = Time_b,
        d  = Status_b,
        x2 = X_b[, "x2"],
        x3 = X_b[, "x3"],
        x4 = X_b[, "x4"],
        x6 = X_b[, "x6"]
      )
      
      coxfit_b <- try(
        coxph(Surv(t, d) ~ x2 + x3 + x4 + x6, data = boot_train_df),
        silent = TRUE
      )
      if (inherits(coxfit_b, "try-error")) next
      
      bh_b <- basehaz(coxfit_b, centered = FALSE)
      S0_b_grid <- exp(-bh_b$hazard)
      t_grid_b  <- bh_b$time
      
      idx_b <- pmax(1, findInterval(Time_b, t_grid_b))
      s0_b  <- S0_b_grid[idx_b]
      
      if (any(is.na(s0_b))) {
        s0_b[is.na(s0_b)] <- min(s0_b, na.rm = TRUE)
      }
      
      bootfit <- try(
        em.Logit.Pois(Time_b, Status_b, Time1, Status1,
                      X_b, X1, Z_b, Z1,
                      b.est, beta.est, s0_b, s01_init, emmax, eps),
        silent = TRUE
      )
      
      if (!inherits(bootfit, "try-error")) {
        latency_boot[i, ] <- bootfit$latencyfit
        incidence_boot[i, ] <- bootfit$b
      }
    }
    
    emfit$latency_se <- apply(latency_boot, 2, sd, na.rm = TRUE)
    emfit$incidence_se <- apply(incidence_boot, 2, sd, na.rm = TRUE)
    
    emfit$latency_p <- 2 * (1 - pnorm(abs(emfit$latencyfit / emfit$latency_se)))
    emfit$incidence_p <- 2 * (1 - pnorm(abs(emfit$b / emfit$incidence_se)))
  }
  
  return(emfit)
}


# Spline
em.Spline.Pois <- function(Time, Status, Time1, Status1,
                           X, X1, Z, Z1,
                           b, beta, s0, s01,
                           emmax, eps) {
  
  n <- length(Status)
  s  <- s0
  s1 <- s01
  
  convergence <- 1000
  i <- 1
  
  while (convergence > eps && i <= emmax) {
    UN <- matrix(exp(Z %*% b)/(1+exp(Z %*% b)),ncol=1)
    PRED <- matrix(exp(Z1 %*% b)/(1+exp(Z1 %*% b)),ncol=1)
    
    if(is.null(beta) || length(beta) != (ncol(X) - 1)) {
      beta <- rep(0, ncol(X) - 1)
    }
    
    survival  <- drop(s^(exp(X[, -1, drop=FALSE] %*% beta)))
    survival1 <- drop(s1^(exp(X1[, -1, drop=FALSE] %*% beta)))
    
    # E-STEP: Using matched probabilities for Train (UN) and Test (PRED)
    M <- Status - (survival * log(pmax(1 - UN, 1e-6)))
    M1 <- Status1 - (survival1 * log(pmax(1 - PRED, 1e-6)))
    
    # Incidence Part (M-STEP)
    Q1 <- function(par) {
      bb <- par
      u_temp <- matrix(exp(Z %*% bb)/(1+exp(Z %*% bb)),ncol=1)
      loglik <- sum(M*log(-log(pmax(1-u_temp, 1e-10)))) + sum(log(pmax(1-u_temp, 1e-10)))
      return(-loglik)
    }
    
    update_b = optim(par=b,fn=Q1,method="Nelder-Mead")$par 
    
    # Latency Part (M-STEP)
    fit_w <- coxph(Surv(Time, Status) ~ X[, -1, drop = FALSE] + offset(log(pmax(M, 1e-4))),
                   subset = M > 0, method = "breslow")
    update_beta <- fit_w$coef
    
    update_s <- smsurv(Time, Status, X, beta, w = M, model = "ph")$survival
    update_s1 <- smsurv(Time1, Status1, X1, beta, w = M1, model = "ph")$survival
    
    convergence <- sum((update_b - b)^2) + sum((update_beta - beta)^2)
    
    b <- update_b
    beta <- update_beta 
    s <- update_s
    s1 <- update_s1
    
    i <- i+1
  }
  
  # Final calculation for returns
  UN <- matrix(exp(Z %*% b)/(1+exp(Z %*% b)),ncol=1)
  PRED <- matrix(exp(Z1 %*% b)/(1+exp(Z1 %*% b)),ncol=1)
  survival  <- drop(s^(exp(X[, -1, drop=FALSE] %*% beta)))
  survival1 <- drop(s1^(exp(X1[, -1, drop=FALSE] %*% beta)))
  Sp <- (1 - UN)^(1 - survival)
  Sp.pred <- (1 - PRED)^(1 - survival1)
  S1 = (Sp-(1-UN))/UN 
  S1.pred = (Sp.pred-(1-PRED))/PRED
  
  return(list(
    b = b,
    latencyfit = beta,
    UN = UN,
    PRED = PRED,
    Sp = Sp,
    Sp.pred = Sp.pred,
    S1 = S1,
    S1.pred = S1.pred,
    s0 = s,
    s01 = s1,
    S = survival,
    S.pred = survival1,
    tau = convergence
  ))
}

smcure.Spline.Pois <- function(train, test,  Var = TRUE, emmax = 500, eps = 1e-3, nboot = 100){
  
  Time <- train$t; Status <- train$d
  Time1 <- test$t; Status1 <- test$d
  
  X <- model.matrix(~ x2 + x3 + x4 + x6, data = train)
  X1 <- model.matrix(~ x2 + x3 + x4 + x6, data = test)
  
  #Scaling age and tumor thickness
  cols_scale <- colnames(X) %in% c("x2", "x6")
  scale_params <- list(
    x2 = list(mean = mean(X[, "x2"]), sd = sd(X[, "x2"])),
    x6 = list(mean = mean(X[, "x6"]), sd = sd(X[, "x6"]))
  )
  X[, cols_scale] <- scale(X[, cols_scale])
  X1[, "x2"] <- (X1[, "x2"] - scale_params$x2$mean) / scale_params$x2$sd
  X1[, "x6"] <- (X1[, "x6"] - scale_params$x6$mean) / scale_params$x6$sd
  
  Z <- X; Z1 <- X1
  
  
  
  coxfit_train <- coxph(Surv(Time, Status) ~ 1, data = train)
  coxfit_test <- coxph(Surv(Time1, Status1) ~ 1, data = test)
  
  out.data <- basehaz(coxfit_train, centered = FALSE)  # columns: hazard, time
  out.data1 <- basehaz( coxfit_test, centered = FALSE)  # columns: hazard, time
  t_grid  <- out.data$time
  t_grid1  <- out.data1$time
  idx_tr <- pmax(1, findInterval(Time,  t_grid))
  idx_te <- pmax(1, findInterval(Time1, t_grid1))
  S0_grid <- exp(-out.data$hazard)
  S01_grid <- exp(-out.data1$hazard)
  
  
  # initial full versions
  s0_full  <- exp(-out.data[,1])
  s01_full <- exp(-out.data1[,1])
  
  # fallback indexed versions
  s0_idx  <- S0_grid[idx_tr]
  s01_idx <- S01_grid[idx_te]
  
  
  s0_init  <- S0_grid # length(Time)
  s01_init <- S01_grid  # length(Time1)
  
  
  
  
  
  if(any(is.na(s0_init))) s0_init[is.na(s0_init)] <- min(s0_init, na.rm = TRUE)
  if(any(is.na(s01_init))) s01_init[is.na(s01_init)] <- min(s01_init, na.rm = TRUE)
  
 
  df_cont <- 2
  
  # Basis for Training
  ns_x2 <- splines::ns(train$x2, df = df_cont)
  ns_x6 <- splines::ns(train$x6, df = df_cont)
  
  Z <- cbind(
    1,
    ns_x2,
    ns_x6,
    train$x3,
    train$x4
  )
  
  # Basis for Testing
  Z1 <- cbind(
    1,
    predict(ns_x2, test$x2),
    predict(ns_x6, test$x6),
    test$x3,
    test$x4
  )
  
  b_start <- rep(0, ncol(Z))
  beta_start <- coxfit_train$coefficients 
  
  emfit <- em.Spline.Pois(Time, Status, Time1, Status1, X, X1, Z, Z1, b_start, beta_start, s0_init, s01_init, emmax, eps)
  
  if (Var) {
    cat("Starting bootstrap (", nboot, " iterations)...\n")
    
    latency_boot <- matrix(NA_real_, nrow = nboot, ncol = length(emfit$latencyfit))
    incidence_boot <- matrix(NA_real_, nrow = nboot, ncol = length(emfit$b))
    
    for (i in 1:nboot) {
      cat("Bootstrap", i, "of", nboot, "\n")
      boot_idx <- sample(seq_along(Status), length(Status), replace = TRUE)
      
      Time_b   <- Time[boot_idx]
      Status_b <- Status[boot_idx]
      X_b <- X[boot_idx, , drop = FALSE]
      Z_b <- Z[boot_idx, , drop = FALSE]
      
      boot_train_df <- data.frame(
        t  = Time_b,
        d  = Status_b,
        x2 = X_b[, "x2"],
        x3 = X_b[, "x3"],
        x4 = X_b[, "x4"],
        x6 = X_b[, "x6"]
      )
      
      coxfit_b <- try(
        coxph(Surv(t, d) ~ x2 + x3 + x4 + x6, data = boot_train_df),
        silent = TRUE
      )
      if (inherits(coxfit_b, "try-error")) next
      
      bh_b <- basehaz(coxfit_b, centered = FALSE)
      S0_b_grid <- exp(-bh_b$hazard)
      t_grid_b  <- bh_b$time
      
      idx_b <- pmax(1, findInterval(Time_b, t_grid_b))
      s0_b  <- S0_b_grid[idx_b]
      
      if (any(is.na(s0_b))) {
        s0_b[is.na(s0_b)] <- min(s0_b, na.rm = TRUE)
      }
      
      bootfit <- try(
        em.Spline.Pois(Time_b, Status_b, Time1, Status1,
                       X_b, X1, Z_b, Z1,
                       emfit$b, emfit$latencyfit,
                       s0_b, s01_init, emmax, eps),
        silent = TRUE
      )
      
      if (!inherits(bootfit, "try-error")) {
        latency_boot[i, ] <- bootfit$latencyfit
        incidence_boot[i, ] <- bootfit$b
      }
    }
    
    emfit$latency_se <- apply(latency_boot, 2, sd, na.rm = TRUE)
    emfit$incidence_se <- apply(incidence_boot, 2, sd, na.rm = TRUE)
    
    emfit$latency_p <- 2 * (1 - pnorm(abs(emfit$latencyfit / emfit$latency_se)))
    emfit$incidence_p <- 2 * (1 - pnorm(abs(emfit$b / emfit$incidence_se)))
  }
  
  
  
  return(emfit)
}




# DECISION TREE
em.DT.Pois <- function(Time, Status, Time1, Status1,
                       X, X1, Z, Z1,
                       beta, s0, s01,
                       uncureprob, uncurepred,
                       emmax, eps, best_params) {
  
  n <- length(Status)
  m <- length(Status1)
  s <- s0
  s1 <- s01
  UN   <- uncureprob
  PRED <- uncurepred
  
  
  
  convergence <- 1000
  i <- 1
  
  while (convergence > eps && i <= emmax) {
    
    if(is.null(beta) || length(beta) != (ncol(X) - 1)) {
      beta <- rep(0, ncol(X) - 1)
    }
    
    # Latency survival update
    survival  <- drop(s^(exp(X[, -1, drop = FALSE] %*% beta)))
    survival1 <- drop(s1^(exp(X1[, -1, drop = FALSE] %*% beta)))
    
    # E-STEP: Calculate posterior probability of being uncured
    w_prob <- Status + (1-Status)*(1-((1-UN)^(survival)))
    w_prob <- pmin(pmax(w_prob, 1e-6), 1 - 1e-6)
    M  <- Status - (survival * log(pmax(1 - UN, 1e-6)))
    M1 <- Status1 - (survival1 * log(pmax(1 - PRED, 1e-6)))
    
    # M-STEP: Incidence Part using Data Augmentation (K=5)
    K <- 5
    V_matrix <- matrix(rbinom(n * K, size = 1, prob = rep(w_prob, each = K)), nrow = n, byrow = TRUE)
    
    cure_preds <- matrix(NA, nrow = n, ncol = K)
    pred_preds <- matrix(NA, nrow = m, ncol = K)
    for (k in 1:K) {
      yk <- as.factor(V_matrix[, k])
      yk <- factor(V_matrix[, k], levels = c(0,1), labels = c("cured","uncured"))
      
      mod_data <- data.frame(Z[, -1, drop = FALSE])
      mod_data$yk <- yk
      
      mod <- rpart(yk ~ ., data = mod_data, method = "class", control = rpart.control(
        cp = best_params$cp,
        minsplit = best_params$minsplit,
        maxdepth = best_params$maxdepth
      ))
      
      probs_train <- predict(mod, newdata = as.data.frame(Z[, -1, drop = FALSE]), type = "prob")
      probs_test <- predict(mod, newdata = as.data.frame(Z1[, -1, drop = FALSE]), type = "prob")
      
      cure_preds[, k] <- probs_train[, "uncured"]
      pred_preds[, k] <- probs_test[, "uncured"]
    }
    
    update_cureb <- rowMeans(cure_preds, na.rm = TRUE)
    update_pred  <- rowMeans(pred_preds, na.rm = TRUE)
    # M-step for beta (Latency)
    fit_w <- coxph(Surv(Time, Status) ~ X[, -1, drop = FALSE] + offset(log(pmax(M, 1e-4))), 
                   subset = M != 0, method = "breslow")
    update_beta <- fit_w$coef
    
    # Update baseline survival
    update_s  <- smsurv(Time, Status, X, beta, w = M, model = "ph")$survival
    update_s1 <- smsurv(Time1, Status1, X1, beta, w = M1, model = "ph")$survival
    
    convergence <- sum(c(update_beta-beta,mean(update_cureb)-mean(UN),mean(update_s)-mean(s))^2)
    
    UN   <- update_cureb
    PRED <- update_pred
    beta <- update_beta
    s    <- update_s
    s1   <- update_s1
    i    <- i + 1
  }
  
  Sp      = (1-UN)^(1-s)
  Sp.pred = (1-PRED)^(1-s1) 
  S1      = (Sp-(1-UN))/pmax(UN, 1e-9)
  S1.pred = (Sp.pred-(1-PRED))/pmax(PRED, 1e-9)
  
  return(list(latencyfit = beta, UN = UN, PRED = PRED,
              Sp = Sp, Sp.pred = Sp.pred, S1 = S1, S1.pred = S1.pred, S.pred = s1,
              s0 = s, S = s, tau = convergence,best_params))
}

smcure.DT.Pois <- function(train, test, Var = TRUE, emmax = 500, eps = 1e-3, nboot = 100) {
  Time <- train$t; Status <- train$d
  Time1 <- test$t; Status1 <- test$d
  X <- model.matrix(~ x2 + x3 + x4 + x6, data = train)
  X1 <- model.matrix(~ x2 + x3 + x4 + x6, data = test)
  # Standardize
  cols_scale <- colnames(X) %in% c("x2", "x6")
  train_scaled <- scale(X[, cols_scale])
  X[, cols_scale] <- train_scaled
  X1[, cols_scale] <- scale(X1[, cols_scale], center = attr(train_scaled, "scaled:center"), scale = attr(train_scaled, "scaled:scale"))
  
  Z <- X; Z1 <- X1
  
  
  coxfit_train <- coxph(Surv(Time, Status) ~ 1, data = train)
  coxfit_test <- coxph(Surv(Time1, Status1) ~ 1, data = test)
  
  
  out.data <- basehaz(coxfit_train, centered = FALSE)  # columns: hazard, time
  S0_grid <- exp(-out.data[,1])
  
  
  out.data1 <- basehaz( coxfit_test, centered = FALSE)  # columns: hazard, time
  S01_grid <- exp(-out.data1[,1])
  
  
  
  
  s0_init  <- S0_grid # length(Time)
  s01_init <- S01_grid  # length(Time1)
  
  
  # --- Pre-tuning of Decision Tree  ---
  nw <- factor(Status, levels = c(0,1), labels = c("cured","uncured"))
  Zdt <- as.data.frame(Z[, -1, drop = FALSE])
  K <- 10; set.seed(1)
  pos <- which(nw == "uncured"); neg <- which(nw == "cured")
  fpos <- split(sample(pos), rep(1:K, length.out = length(pos)))
  fneg <- split(sample(neg), rep(1:K, length.out = length(neg)))
  folds <- lapply(1:K, function(k) sort(c(fpos[[k]], fneg[[k]])))
  auc_fast <- function(y, p){ y <- as.integer(y=="uncured"); n1<-sum(y==1); n0<-sum(y==0); if(n1==0||n0==0) return(NA_real_); r<-rank(p,ties.method="average"); (sum(r[y==1]) - n1*(n1+1)/2)/(n1*n0) }
  
  
  
  ms_grid <- c(2, 3, 4)         
  md_grid <- c(28, 30, 32, 35)  
  cp_grid <- c(0, 0.00001, 0.00005) 
  
  
  best_auc <- -Inf
  best_params <- list(cp = 0.0001, minsplit = 2, maxdepth = 30)
  
  for (cp_val in cp_grid) {
    for (ms_val in ms_grid) {
      for (md_val in md_grid) {
        
        y_all <- c(); p_all <- c()
        
        for (k in 1:K) {
          vl <- folds[[k]]
          tr <- setdiff(seq_len(nrow(Zdt)), vl)
          
          if (length(unique(nw[tr])) < 2 || length(unique(nw[vl])) < 2) next
          
          fit <- try(
            rpart::rpart(
              nw ~ .,
              data = data.frame(Zdt, nw = nw)[tr, ],
              method = "class",
              control = rpart::rpart.control(
                cp = cp_val,
                minsplit = ms_val,
                maxdepth = md_val
              )
            ),
            silent = TRUE
          )
          if (inherits(fit, "try-error")) next
          
          pv <- try(
            predict(fit, newdata = Zdt[vl, , drop = FALSE], type = "prob")[, "uncured"],
            silent = TRUE
          )
          if (inherits(pv, "try-error")) next
          
          y_all <- c(y_all, nw[vl])
          p_all <- c(p_all, pv)
        }
        
        auc_val <- if (length(y_all) > 1) auc_fast(y_all, p_all) else NA_real_
        
        if (!is.na(auc_val) && auc_val > best_auc) {
          best_auc <- auc_val
          best_params <- list(
            cp = cp_val,
            minsplit = ms_val,
            maxdepth = md_val
          )
        }
      }
    }
  }
  
  initial_mod <- rpart::rpart(nw ~ ., data = data.frame(Zdt, nw = nw), method = "class", control = rpart::rpart.control(cp = best_params$cp))
  
  uncureprob <- predict(initial_mod, newdata = as.data.frame(Z[, -1, drop = FALSE]), type = "prob")[, "uncured"]
  uncurepred <- predict(initial_mod, newdata = as.data.frame(Z1[, -1, drop = FALSE]), type = "prob")[, "uncured"]
  
  
  
  
  
  emfit <- em.DT.Pois(Time, Status, Time1, Status1,
                      X, X1, Z, Z1,
                      coxfit_train$coefficients,
                      s0_init, s01_init,
                      uncureprob, uncurepred,
                      emmax, eps, best_params)
  if (Var) {
    cat("Starting bootstrap (", nboot, " iterations)...\n")
    latency_boot <- matrix(NA_real_, nboot, length(emfit$latencyfit))
    for (i in 1:nboot) {
      cat("Bootstrap", i, "of", nboot, "\n")
      boot_idx <- sample(1:nrow(train), replace = TRUE)
      Time_b   <- Time[boot_idx]
      Status_b <- Status[boot_idx]
      X_b      <- X[boot_idx, , drop = FALSE]
      Z_b      <- Z[boot_idx, , drop = FALSE]
      
      boot_train_df <- data.frame(
        t  = Time_b,
        d  = Status_b,
        x2 = X_b[, "x2"],
        x3 = X_b[, "x3"],
        x4 = X_b[, "x4"],
        x6 = X_b[, "x6"]
      )
      
      coxfit_b <- try(
        coxph(Surv(t, d) ~ x2 + x3 + x4 + x6, data = boot_train_df),
        silent = TRUE)
      
      if (inherits(coxfit_b, "try-error")) next
      
      bh_b <- basehaz(coxfit_b, centered = FALSE)
      S0_b_grid <- exp(-bh_b$hazard)
      t_grid_b  <- bh_b$time
      
      idx_b <- pmax(1, findInterval(Time_b, t_grid_b))
      s0_b  <- S0_b_grid[idx_b]
      
      if (any(is.na(s0_b))) {
        s0_b[is.na(s0_b)] <- min(s0_b, na.rm = TRUE)
      }
      
      b_fit <- try(
        em.DT.Pois(Time_b, Status_b, Time1, Status1, 
                   X_b, X1, Z_b, Z1, 
                   emfit$latencyfit, s0_b, s01_init, 
                   uncureprob[boot_idx], uncurepred,
                   emmax, eps, best_params),
        silent = TRUE)
      if (!inherits(b_fit, "try-error")) latency_boot[i, ] <- b_fit$latencyfit
    }
    cat("Successful DT bootstrap fits:", sum(complete.cases(latency_boot)), "out of", nboot, "\n")
    emfit$latency_se <- apply(latency_boot, 2, sd, na.rm = TRUE)
    emfit$latency_p <- 2 * (1 - pnorm(abs(emfit$latencyfit / emfit$latency_se)))
  }
  return(emfit)
}








# SUPPORT VECTOR MACHINE

em.SVM.Pois <- function(Time, Status, Time1, Status1,
                        X, X1, Z, Z1,
                        beta, s0, s01,
                        uncureprob, uncurepred,
                        emmax, eps, best_params) {
  
  
  n <- length(Status)
  m <- length(Status1)
  s <- s0; s1 <- s01
  UN <- uncureprob; PRED <- uncurepred
  
  
  convergence <- 1000
  i <- 1
  
  while (convergence > eps && i <= emmax) {
    
    if(is.null(beta) || length(beta) != (ncol(X) - 1)) {
      beta <- rep(0, ncol(X) - 1)
    }
    
    # Latency survival
    survival  <- drop(s^(exp(X[, -1, drop = FALSE] %*% beta)))
    survival1 <- drop(s1^(exp(X1[, -1, drop = FALSE] %*% beta)))
    
    # E-STEP: Calculate posterior probability of being uncured
    w_prob <- Status + (1-Status)*(1-((1-UN)^(survival)))
    w_prob <- pmin(pmax(w_prob, 1e-5), 1 - 1e-5)
    M  <- Status - (survival * log(pmax(1 - UN, 1e-6)))
    M1 <- Status1 - (survival1 * log(pmax(1 - PRED, 1e-6)))
    
    # M-STEP: Incidence Part using Data Augmentation (K=5)
    K <- 5
    V_matrix <- matrix(rbinom(n * K, size = 1, prob = rep(w_prob, each = K)), nrow = n, byrow = TRUE)
    V_matrix<- (V_matrix*2)-1
    cure_preds <- matrix(NA, nrow = n, ncol = K)
    pred_preds <- matrix(NA, nrow = m, ncol = K)
    
    for (k in 1:K) {
      yk <- as.factor(V_matrix[, k])
      if (length(levels(yk)) < 2) {
        val <- if(levels(yk)[1] == "1") 1 else 0
        cure_preds[, k] <- val
        pred_preds[, k] <- val
        next
      }
      
      mod <- svm(Z[, -1, drop = FALSE], yk,gamma = best_params$gamma, cost = best_params$cost,probability = TRUE)
      
      p_train_attr <- predict(mod, Z[, -1, drop = FALSE], probability = TRUE)
      p_test_attr <- predict(mod, Z1[, -1, drop = FALSE], probability = TRUE)
      
      
      p_train <- attr(p_train_attr, "probabilities")
      p_test  <- attr(p_test_attr, "probabilities")
      
      
      
      
      if ("1" %in% colnames(p_train)) {
        cure_preds[, k] <- p_train[, "1"]
      } else {
        cure_preds[, k] <- 0 
      }
      
      if ("1" %in% colnames(p_test)) {
        pred_preds[, k] <- p_test[, "1"]
      } else {
        pred_preds[, k] <- 0
      }
    }
    
    update_cureb <- rowMeans(cure_preds, na.rm = TRUE)
    update_pred  <- rowMeans(pred_preds, na.rm = TRUE)
    
    
    # M-step for beta (Latency)
    fit_w <- coxph(Surv(Time, Status) ~ X[, -1, drop = FALSE] + offset(log(pmax(M, 1e-6))), 
                   subset = M != 0, method = "breslow")
    update_beta <- fit_w$coef
    
    # Update baseline survival
    update_s  <- smsurv(Time, Status, X, beta, w = M, model = "ph")$survival
    update_s1 <- smsurv(Time1, Status1, X1, beta, w = M1, model = "ph")$survival
    
    # Convergence on both latency and incidence parameters
    convergence <- sum((update_beta - beta)^2, na.rm = TRUE) + mean((update_cureb - UN)^2, na.rm = TRUE)
    
    UN   <- update_cureb
    PRED <- update_pred
    beta <- update_beta
    s    <- update_s
    s1   <- update_s1
    i    <- i + 1
  }
  
  survival  <- drop(s^(exp(X[, -1, drop = FALSE] %*% beta)))
  survival1 <- drop(s1^(exp(X1[, -1, drop = FALSE] %*% beta)))
  Sp      = (1-UN)^(1-s)
  Sp.pred = (1-PRED)^(1-s1) 
  S1      = (Sp-(1-UN))/pmax(UN, 1e-9)
  S1.pred = (Sp.pred-(1-PRED))/pmax(PRED, 1e-9)
  
  return(list(latencyfit = beta, UN = UN, PRED = PRED,
              Sp = Sp, Sp.pred = Sp.pred, S1 = S1, S1.pred = S1.pred, S.pred = s1,
              s0 = s, s01 = s1, S = s, tau = convergence,
              iterations = i , best_params=best_params))
}

smcure.SVM.Pois <- function(train, test, Var = TRUE, emmax = 500, eps = 1e-3, nboot = 100) {
  Time <- train$t; Status <- train$d
  Time1 <- test$t; Status1 <- test$d
  
  n <- length(Status)
  m <- length(Status1)
  
  
  X <- model.matrix(~ x2 + x3 + x4 + x6, data = train)
  X1 <- model.matrix(~ x2 + x3 + x4 + x6, data = test)
  
  # Standardize features (Essential for SVM kernels)
  cols_scale <- colnames(X) %in% c("x2", "x6")
  train_scaled <- scale(X[, cols_scale])
  X[, cols_scale] <- train_scaled
  X1[, cols_scale] <- scale(X1[, cols_scale], 
                            center = attr(train_scaled, "scaled:center"), 
                            scale = attr(train_scaled, "scaled:scale")) 
  
  
  Z <- X; Z1 <- X1
  w <- Status
  nw <- as.factor(w * 2 - 1)
  
  
  
  Z_svm <- as.data.frame(Z[, -1, drop = FALSE])
  
  obj <- tune.svm(
    x = Z_svm,
    y = nw,
    kernel = "radial",
    gamma = 3^seq(-6, -4, by = 3), 
    cost  = 3^seq(4, 6, by = ),
    tunecontrol = tune.control(sampling = "cross", cross = 10)
  )
  
  best_params <- obj$best.parameters
  
  
  mod <- tryCatch(
    svm(
      Z[, -1, drop = FALSE],
      nw,
      gamma = best_params$gamma,
      cost = best_params$cost,
      probability = TRUE
    ),
    error = function(e) NULL
  )
  
  pred  <- predict(mod, Z[, -1, drop = FALSE], probability = TRUE)
  cpred <- predict(mod, Z1[, -1, drop = FALSE], probability = TRUE)
  
  proba  <- attr(pred,  "probabilities")
  cproba <- attr(cpred, "probabilities")
  
  uncureprob<-c(1,1)
  uncurepred<-c(1,1)
  
  
  for (i in 1:n){uncureprob[i]<-proba[i,colnames(proba)==1]}
  for (d in 1:m){uncurepred[d]<-cproba[d,colnames(cproba)==1]}
  
  
  
  
  
  coxfit_train <- coxph(Surv(Time, Status) ~  1, data = train)
  coxfit_test <- coxph(Surv(Time1, Status1) ~ 1, data = test)
  out.data <- basehaz(coxfit_train, centered = FALSE)  # columns: hazard, time
  out.data1 <- basehaz( coxfit_test, centered = FALSE)  # columns: hazard, time
  t_grid  <- out.data$time
  t_grid1  <- out.data1$time
  idx_tr <- pmax(1, findInterval(Time,  t_grid))
  idx_te <- pmax(1, findInterval(Time1, t_grid1))
  S0_grid <- exp(-out.data$hazard)
  S01_grid <- exp(-out.data1$hazard)
  
  
  # initial full versions
  s0_full  <- exp(-out.data[,1])
  s01_full <- exp(-out.data1[,1])
  
  # fallback indexed versions
  s0_idx  <- S0_grid[idx_tr]
  s01_idx <- S01_grid[idx_te]
  
  
  
  
  # choose based on length match
  if (length(s0_full) == length(Time)) {
    s0_init <- s0_full
  } else {
    s0_init <- s0_idx
  }
  
  if (length(s01_full) == length(Time1)) {
    s01_init <- s01_full
  } else {
    s01_init <- s01_idx
  } 
  
  
  
  emfit <- em.SVM.Pois(Time, Status, Time1, Status1, X, X1, Z, Z1,
                       coxfit_train$coefficients, s0_init, s01_init,
                       uncureprob, uncurepred,
                       emmax, eps, best_params)
  
  if (Var) {
    n_latency <- length(emfit$latencyfit)
    latency_boot <- matrix(NA_real_, nrow = nboot, ncol = n_latency)
    
    cat("Starting SVM bootstrap (", nboot, " iterations)...\n")
    
    for (i in 1:nboot) {
      cat("Bootstrap", i, "of", nboot, "\n")
      boot_idx <- sample(seq_along(Status), length(Status), replace = TRUE)
      
      Time_b   <- Time[boot_idx]
      Status_b <- Status[boot_idx]
      X_b      <- X[boot_idx, , drop = FALSE]
      Z_b      <- Z[boot_idx, , drop = FALSE]
      
      boot_train_df <- data.frame(
        t  = Time_b,
        d  = Status_b,
        x2 = X_b[, "x2"],
        x3 = X_b[, "x3"],
        x4 = X_b[, "x4"],
        x6 = X_b[, "x6"]
      )
      
      coxfit_b <- try(
        coxph(Surv(t, d) ~ x2 + x3 + x4 + x6, data = boot_train_df),
        silent = TRUE
      )
      if (inherits(coxfit_b, "try-error")) next
      
      bh_b <- basehaz(coxfit_b, centered = FALSE)
      S0_b_grid <- exp(-bh_b$hazard)
      t_grid_b  <- bh_b$time
      
      idx_b <- pmax(1, findInterval(Time_b, t_grid_b))
      s0_b  <- S0_b_grid[idx_b]
      
      if (any(is.na(s0_b))) {
        s0_b[is.na(s0_b)] <- min(s0_b, na.rm = TRUE)
      }
      
      bootfit <- try(
        em.SVM.Pois(Time_b, Status_b, Time1, Status1,
                    X_b, X1, Z_b, Z1,
                    emfit$latencyfit, s0_b, s01_init,
                    uncureprob[boot_idx], uncurepred,
                    emmax, eps,best_params),
        silent = TRUE
      )
      
      if (!inherits(bootfit, "try-error")) {
        latency_boot[i, ] <- bootfit$latencyfit
      }
    }
    cat("Successfulbootstrap fits:", sum(complete.cases(latency_boot)), "out of", nboot, "\n")
    emfit$latency_se <- apply(latency_boot, 2, sd, na.rm = TRUE)
    emfit$latency_p  <- 2 * (1 - pnorm(abs(emfit$latencyfit / emfit$latency_se)))
  }
  return(emfit)
}


#NEURAL NETWORK
em.NN.Pois <- function(Time, Status, Time1, Status1,
                       X, X1, Z, Z1,
                       beta, s0, s01,
                       initial_un, initial_pred,
                       emmax, eps, best_params, stepmax) {
  
  n <- length(Status)
  m <- length(Status1)
  s <- s0; s1 <- s01
  UN <- initial_un; PRED <- initial_pred
  
  convergence <- 1000
  i <- 1
  X_train_nn <- as.data.frame(Z[, -1, drop = FALSE])
  X_test_nn  <- as.data.frame(Z1[, -1, drop = FALSE])
  colnames(X_train_nn) <- paste0("Input_", seq_len(ncol(X_train_nn)))
  colnames(X_test_nn)  <- paste0("Input_", seq_len(ncol(X_test_nn)))
  
  current_weights <- NULL
  
  while (convergence > eps && i <= emmax) {
    
    if(is.null(beta) || length(beta) != (ncol(X) - 1)) {
      beta <- rep(0, ncol(X) - 1)
    }
    
    survival  <- drop(s^(exp(X[, -1, drop = FALSE] %*% beta)))
    survival1 <- drop(s1^(exp(X1[, -1, drop = FALSE] %*% beta)))
    
    # E-STEP
    w_prob <- Status + (1 - Status) * (1 - ((1 - UN)^(survival)))
    w_prob <- pmin(pmax(w_prob, 1e-6), 1 - 1e-6)
    
    # M-STEP: Incidence Part
    K <- 5
    V_matrix <- matrix(rbinom(n * K, size = 1, prob = rep(w_prob, each = K)), nrow = n, byrow = TRUE)
    target_soft <- rowMeans(V_matrix)
    train_df <- cbind(target = target_soft, X_train_nn)
    
    nn_mod <- try(neuralnet::neuralnet(
      target ~ .,
      data = train_df,
      hidden = best_params,
      linear.output = FALSE,
      startweights = current_weights,
      stepmax = 5e5, 
      threshold = 0.08, 
      learningrate.limit = list(min = 1e-8, max = 0.1),
      lifesign = "none"
    ), silent = TRUE)
    
    if (!inherits(nn_mod, "try-error") && !is.null(nn_mod$weights)) {
      current_weights <- nn_mod$weights
      p_tr <- as.numeric(neuralnet::compute(nn_mod, covariate = X_train_nn)$net.result)
      p_te <- as.numeric(neuralnet::compute(nn_mod, covariate = X_test_nn)$net.result)
    } else {
      glm_fit <- glm(target ~ ., data = train_df, family = quasibinomial())
      p_tr <- predict(glm_fit, newdata = X_train_nn, type = "response")
      p_te <- predict(glm_fit, newdata = X_test_nn, type = "response")
    }
    update_cureb <- pmin(pmax(p_tr, 1e-6), 1 - 1e-6)
    update_pred  <- pmin(pmax(p_te, 1e-6), 1 - 1e-6)
    
    
    # M-step: Latency (CoxPH)
    M <- Status - (survival * log(pmax(1 - update_cureb, 1e-5)))
    M1 <- Status1 - (survival1 * log(pmax(1 -  update_pred, 1e-5)))
    fit_w <- try(coxph(Surv(Time, Status) ~ X[, -1, drop = FALSE] + offset(log(pmax(M, 1e-4))), 
                       subset = M > 0, method = "breslow"), silent = TRUE)
    
    update_beta <- if(inherits(fit_w, "try-error")) beta else fit_w$coef
    update_s <- smsurv(Time, Status, X,beta, w = M, model = "ph")$survival
    update_s1 <- smsurv(Time1, Status1, X1,beta, w = M, model = "ph")$survival
    
    convergence <- sum((update_beta - beta)^2, na.rm = TRUE) + mean((update_cureb - UN)^2)
    
    UN <- update_cureb; PRED <- update_pred; beta <- update_beta
    s <- update_s
    s1 <- update_s1
    
    i <- i + 1
  }
  
  Sp <- (1 - UN)^(1 - s); Sp.pred <- (1 - PRED)^(1 - s1)
  return(list(latencyfit = beta, UN = UN, PRED = PRED, Sp = Sp, Sp.pred = Sp.pred,
              s0 = s, s01 = s1, S = s, S.pred = s1, 
              tau = convergence, iterations = i - 1))
}

smcure.NN.Pois <- function(train, test, Var = TRUE, emmax = 100, eps = 1e-3, nboot = 100) {
  Time <- train$t; Status <- train$d; Time1 <- test$t; Status1 <- test$d
  X <- model.matrix(~ x2 + x3 + x4 + x6, data = train); X1 <- model.matrix(~ x2 + x3 + x4 + x6, data = test)
  
  cols_scale <- colnames(X) %in% c("x2", "x6")
  train_scaled <- scale(X[, cols_scale])
  X[, cols_scale] <- train_scaled
  X1[, cols_scale] <- scale(X1[, cols_scale], center = attr(train_scaled, "scaled:center"), scale = attr(train_scaled, "scaled:scale"))
  Z <- X; Z1 <- X1
  
  Z_tr_mat <- as.matrix(as.data.frame(lapply(as.data.frame(Z[, -1, drop = FALSE]), as.numeric)))
  
  
  coxfit_train <- coxph(Surv(Time, Status) ~ 1, data = train)
  coxfit_test <- coxph(Surv(Time1, Status1) ~ 1, data = test)
  
  
  out.data <- basehaz(coxfit_train, centered = FALSE)  # columns: hazard, time
  S0_grid <- exp(-out.data[,1])
  
  
  out.data1 <- basehaz( coxfit_test, centered = FALSE)  # columns: hazard, time
  S01_grid <- exp(-out.data1[,1])
  
  
  
  
  s0_init  <- S0_grid # length(Time)
  s01_init <- S01_grid  # length(Time1)
  
  ybin <- as.integer(Status == 1)
  tune_data <- cbind.data.frame(y = ybin, Z_tr_mat)
  hidden_grid <- list( c(2),c(3), c(4),c(5),c(6), c(3,2),c(4,2), c(5,2),c(6,3))
  
  
  
  k_folds <- 10
  folds <- split(sample(1:nrow(tune_data)), rep(1:k_folds, length.out = nrow(tune_data)))
  cv_scores <- rep(NA, length(hidden_grid))
  
  for(h in seq_along(hidden_grid)) {
    auc_f <- c()
    for(k in 1:k_folds) {
      idx_va <- folds[[k]]; idx_tr <- setdiff(1:nrow(tune_data), idx_va)
      nn <- try(neuralnet::neuralnet(y ~ ., data = tune_data[idx_tr,], hidden = hidden_grid[[h]], 
                                     linear.output=F, stepmax=5e5, threshold=0.08), silent=T)
      if(inherits(nn, "try-error")) next
      p <- as.numeric(neuralnet::compute(nn, tune_data[idx_va, -1])$net.result)
      auc_f <- c(auc_f, as.numeric(pROC::auc(pROC::roc(tune_data$y[idx_va], p, quiet=T, direction="<"))))
    }
    cv_scores[h] <- mean(auc_f, na.rm=T)
  }
  
  best_params <- hidden_grid[[which.max(cv_scores)]]
  
  emfit <- em.NN.Pois(Time, Status, Time1, Status1, X, X1, Z, Z1, 
                      coxfit_train$coefficients, s0_init, s01_init, 
                      rep(0.5, length(Time)), rep(0.5, length(Time1)), 
                      emmax, eps, best_params, 5e5)
  
  if (Var) {
    cat("Starting NN bootstrap (", nboot, " iterations)...\n")
    
    latency_boot <- matrix(NA_real_, nboot, length(emfit$latencyfit))
    
    for (i in 1:nboot) {
      cat("Bootstrap", i, "of", nboot, "\n")
      boot_idx <- sample(1:nrow(train), replace = TRUE)
      
      Time_b   <- Time[boot_idx]
      Status_b <- Status[boot_idx]
      X_b      <- X[boot_idx, , drop = FALSE]
      Z_b      <- Z[boot_idx, , drop = FALSE]
      
      if (length(unique(Status_b)) < 2) next
      
      boot_train_df <- data.frame(
        t  = Time_b,
        d  = Status_b,
        x2 = X_b[, "x2"],
        x3 = X_b[, "x3"],
        x4 = X_b[, "x4"],
        x6 = X_b[, "x6"]
      )
      
      coxfit_b <- try(
        coxph(Surv(t, d) ~ x2 + x3 + x4 + x6, data = boot_train_df),
        silent = TRUE
      )
      
      if (inherits(coxfit_b, "try-error")) next
      
      bh_b <- basehaz(coxfit_b, centered = FALSE)
      S0_b_grid <- exp(-bh_b$hazard)
      t_grid_b  <- bh_b$time
      
      idx_b <- pmax(1, findInterval(Time_b, t_grid_b))
      s0_b  <- S0_b_grid[idx_b]
      
      if (any(is.na(s0_b))) {
        s0_b[is.na(s0_b)] <- min(s0_b, na.rm = TRUE)
      }
      
      b_fit <- try(
        em.NN.Pois(
          Time_b, Status_b, Time1, Status1,
          X_b, X1, Z_b, Z1,
          emfit$latencyfit,
          s0_b, s01_init,
          emfit$UN[boot_idx],
          emfit$PRED,
          emmax, eps,
          best_params,
          5e5
        ),
        silent = TRUE
      )
      
      if (!inherits(b_fit, "try-error")) {
        latency_boot[i, ] <- b_fit$latencyfit
      }
    }
    
    cat("Successful NN bootstrap fits:",
        sum(complete.cases(latency_boot)), "out of", nboot, "\n")
    
    emfit$latency_se <- apply(latency_boot, 2, sd, na.rm = TRUE)
    emfit$latency_p  <- 2 * (1 - pnorm(abs(emfit$latencyfit / emfit$latency_se)))
  }
  return(emfit)
}



#XGBOOST
em.XGB.Pois <- function(Time, Status, Time1, Status1,
                        X, X1, Z, Z1,
                        beta, s0, s01,
                        initial_un, initial_pred,
                        emmax, eps, best_params, nrounds) {
  n <- length(Status)
  m <- length(Status1)
  
  s <- s0; s1 <- s01
  UN <- initial_un; PRED <- initial_pred
  
  
  
  convergence <- 1000
  i <- 1
  
  while (convergence > eps && i <= emmax) {
    
    if (is.null(beta) || length(beta) != (ncol(X) - 1)) {
      beta <- rep(0, ncol(X) - 1)
    }
    
    survival <- drop(s^(exp(X[, -1, drop = FALSE] %*% beta)))
    survival1 <- drop(s1^(exp(X1[, -1, drop = FALSE] %*% beta)))
    
    # E-STEP: Posterior probability of being UNCURED (susceptible)
    w_prob <- Status + (1 - Status) *  (1-((1 - UN)^ survival))
    w_prob <- pmin(pmax(w_prob, 1e-6), 1 - 1e-6)
    M <- Status - (survival * log(pmax(1 - UN, 1e-6)))
    M1 <- Status1 - (survival1 * log(pmax(1 - PRED, 1e-6)))
    
    
    
    
    
    
    
    
    # M-STEP: Incidence Part using Data Augmentation (K=5)
    K <- 5
    V_matrix <- matrix(rbinom(n * K, size = 1, prob = rep(w_prob, each = K)), nrow = n, byrow = TRUE)
    
    cure_preds <- matrix(NA_real_, nrow = n, ncol = K)
    pred_preds <- matrix(NA_real_, nrow = m, ncol = K)
    
    dtest <- xgboost::xgb.DMatrix(data = as.matrix(Z1[, -1, drop = FALSE]))
    for (k in 1:K) {
      dtrain_k <- xgboost::xgb.DMatrix(data = as.matrix(Z[, -1, drop = FALSE]), label = V_matrix[, k])
      xgb_mod <- xgboost::xgb.train(
        params = best_params,
        data = dtrain_k,
        nrounds = nrounds,
        verbose = 0
      )
      cure_preds[, k] <- as.numeric(predict(xgb_mod, dtrain_k))
      pred_preds[, k] <- as.numeric(predict(xgb_mod, dtest))
    }
    
    
    update_cureb <- rowMeans(cure_preds, na.rm = TRUE)
    update_pred <- rowMeans(pred_preds, na.rm = TRUE)
    
    
    df_cox <- data.frame(Time = Time, Status = Status, X[, -1, drop = FALSE])
    fit_w <- coxph(
      Surv(Time, Status) ~ . + offset(log(pmax(M, 1e-4))),
      data = df_cox,
      subset = M != 0,
      method = "breslow"
    )
    update_beta <- fit_w$coef
    
    update_s <- smsurv(Time, Status, X, beta, w = M, model = "ph")$survival
    update_s1 <- smsurv(Time1, Status1, X1, beta, w = M1, model = "ph")$survival
    
    convergence <- sum((update_beta - beta)^2, na.rm = TRUE) +
      mean((update_cureb - UN)^2, na.rm = TRUE) +
      mean((update_s  - s)^2, na.rm = TRUE)
    
    
    UN <- update_cureb; PRED <- update_pred; beta <- update_beta
    s <- update_s; s1 <- update_s1; i <- i + 1
  }
  
  Sp <- (1 - UN)^(1 - s); Sp.pred <- (1 - PRED)^(1 - s1)
  S1 <- (Sp - (1 - UN)) / pmax(UN, 1e-9); S1.pred <- (Sp.pred - (1 - PRED)) / pmax(PRED, 1e-9)
  
  
  
  return(list(
    latencyfit = beta, UN = UN, PRED = PRED,
    Sp = Sp, Sp.pred = Sp.pred, S1 = S1, S1.pred = S1.pred,
    s0 = s, s01 = s1, S = s, S.pred = s1,
    tau = convergence, iterations = i,
    best_params = best_params, nrounds = nrounds
  ))
}

smcure.XGB.Pois <- function(train, test, Var = TRUE, emmax = 500, eps = 1e-3, nboot = 100) {
  Time <- train$t; Status <- train$d
  Time1 <- test$t; Status1 <- test$d
  
  X <- model.matrix(~ x2 + x3 + x4 + x6, data = train)
  X1 <- model.matrix(~ x2 + x3 + x4 + x6, data = test)
  
  
  # Standardize
  cols_scale <- colnames(X) %in% c("x2", "x6")
  train_scaled <- scale(X[, cols_scale])
  X[, cols_scale] <- train_scaled
  X1[, cols_scale] <- scale(X1[, cols_scale], center = attr(train_scaled, "scaled:center"), scale = attr(train_scaled, "scaled:scale"))
  
  Z <- X; Z1 <- X1
  
  coxfit_train <- coxph(Surv(Time, Status) ~ 1, data = train)
  coxfit_test <- coxph(Surv(Time1, Status1) ~ 1, data = test)
  
  
  out.data <- basehaz(coxfit_train, centered = FALSE)  # columns: hazard, time
  S0_grid <- exp(-out.data[,1])
  
  
  out.data1 <- basehaz( coxfit_test, centered = FALSE)  # columns: hazard, time
  S01_grid <- exp(-out.data1[,1])
  
  
  
  
  s0_init  <- S0_grid # length(Time)
  s01_init <- S01_grid  # length(Time1)
  
  
  s0  <- S0_grid # length(Time)
  s01 <- S01_grid  # length(Time1)
  
  if (any(is.na(s0)))  s0[is.na(s0)]   <- min(s0,  na.rm = TRUE)
  if (any(is.na(s01))) s01[is.na(s01)] <- min(s01, na.rm = TRUE)
  
  beta_init <- coxfit_train$coefficients
  
  if (is.null(beta_init) || length(beta_init) != (ncol(X) - 1)) {
    beta_init <- rep(0, ncol(X) - 1)
  } else {
    beta_init <- as.numeric(beta_init)
  }
  
  ## Initial pseudo-labels
  w <- Status
  
  # Numeric labels for XGB
  y_imp <- as.numeric(w)
  
  # Design matrices
  Z_xgb  <- as.matrix(Z[, -1, drop = FALSE])
  Z1_xgb <- as.matrix(Z1[, -1, drop = FALSE])
  
  
  
  # 10-fold CV to tune (eta, nrounds) with early stopping (logloss)
  dtrain_cv <- xgboost::xgb.DMatrix(
    data = Z_xgb,
    label = y_imp
  )
  eta_grid <- c(0.07)
  nrounds_cap <- 1000
  early_stop <- 1000
  
  base_params <- list(
    objective = "binary:logistic",
    max_depth = 5,
    subsample = 1,
    colsample_bytree = 1,
    #colsample_bylevel = 0.8,
    min_child_weight =1,
    gamma = 0,
    lambda = 1 ,
    alpha = 0,
    eval_metric = "auc"
  )
  best_eta <- NA_real_
  best_iter <- NA_integer_
  best_auc <- -Inf
  
  for (eta in eta_grid) {
    params <- modifyList(base_params, list(eta = eta))
    
    cv <- xgboost::xgb.cv(
      params = params,
      data = dtrain_cv,
      nrounds = nrounds_cap,
      nfold = 10,
      stratified = TRUE,
      early_stopping_rounds = early_stop,
      verbose = 0
    )
    
    mean_auc <- max(cv$evaluation_log$test_auc_mean, na.rm = TRUE)
    iter <- cv$best_iteration
    
    if (is.finite(mean_auc) && mean_auc > best_auc) {
      best_auc <- mean_auc
      best_eta <- eta
      best_iter <- ifelse(is.null(iter) || iter == 0, nrounds_cap, iter)
    }
  }
  
  if (!is.finite(best_eta)) {
    best_eta <- 0.03
    best_iter <- 300
  }
  
  best_params <- modifyList(base_params, list(eta = best_eta))
  nrounds <- best_iter
  
  
  # Train final initializer XGB on imputed labels
  dtrain_full <- xgboost::xgb.DMatrix(data = as.matrix(Z[, -1, drop = FALSE]), label = y_imp)
  dtest_full  <- xgboost::xgb.DMatrix(data = as.matrix(Z1[, -1, drop = FALSE]))
  xgb_init <- xgboost::xgb.train(params = best_params, data = dtrain_full, nrounds = nrounds, verbose = 0)
  uncureprob <- pmin(pmax(as.numeric(predict(xgb_init, dtrain_full)), 1e-6), 1 - 1e-6)
  uncurepred <- pmin(pmax(as.numeric(predict(xgb_init, dtest_full)),  1e-6), 1 - 1e-6)
  
  emfit <- em.XGB.Pois(
    Time, Status, Time1, Status1,
    X, X1, Z, Z1,
    beta_init, s0_init, s01_init,
    uncureprob, uncurepred, emmax, eps,
    best_params = best_params, nrounds = nrounds
  )
  
  if (Var) {
    cat("Starting XGB bootstrap (", nboot, " iterations)...\n")
    latency_boot <- matrix(NA_real_, nboot, length(emfit$latencyfit))
    
    for (i in 1:nboot) {
      cat("Bootstrap", i, "of", nboot, "\n")
      boot_idx <- sample(1:nrow(train), replace = TRUE)
      
      Time_b   <- Time[boot_idx]
      Status_b <- Status[boot_idx]
      X_b      <- X[boot_idx, , drop = FALSE]
      Z_b      <- Z[boot_idx, , drop = FALSE]
      
      if (length(unique(Status_b)) < 2) next
      
      boot_train_df <- data.frame(
        t  = Time_b,
        d  = Status_b,
        x2 = X_b[, "x2"],
        x3 = X_b[, "x3"],
        x4 = X_b[, "x4"],
        x6 = X_b[, "x6"]
      )
      
      coxfit_b <- try(
        coxph(Surv(t, d) ~ x2 + x3 + x4 + x6, data = boot_train_df),
        silent = TRUE
      )
      
      if (inherits(coxfit_b, "try-error")) next
      
      bh_b <- basehaz(coxfit_b, centered = FALSE)
      S0_b_grid <- exp(-bh_b$hazard)
      t_grid_b  <- bh_b$time
      
      idx_b <- pmax(1, findInterval(Time_b, t_grid_b))
      s0_b  <- S0_b_grid[idx_b]
      
      if (any(is.na(s0_b))) {
        s0_b[is.na(s0_b)] <- min(s0_b, na.rm = TRUE)
      }
      
      b_fit <- try(
        em.XGB.Pois(
          Time_b, Status_b, Time1, Status1,
          X_b, X1, Z_b, Z1,
          emfit$latencyfit,
          s0_b, s01_init,
          uncureprob[boot_idx], uncurepred,
          emmax, eps, best_params, nrounds
        ),
        silent = TRUE
      )
      
      if (!inherits(b_fit, "try-error")) {
        latency_boot[i, ] <- b_fit$latencyfit
      }
    }
    
    cat("Successful XGB bootstrap fits:",
        sum(complete.cases(latency_boot)), "out of", nboot, "\n")
    emfit$latency_se <- apply(latency_boot, 2, sd, na.rm = TRUE)
    emfit$latency_p  <- 2 * (1 - pnorm(abs(emfit$latencyfit / emfit$latency_se)))
  }
  
 
  return(emfit)
}



#RANDOM FOREST
em.RF.Pois <- function(Time, Status, Time1, Status1, X, X1, Z, Z1,
                       beta, s0, s01,
                       uncureprob, uncurepred,
                       emmax, eps, best_params) { 
  
  n <- length(Status)
  m <- length(Status1)
  s <- s0; s1 <- s01
  UN <- uncureprob; PRED <- uncurepred
  
  convergence <- 1000
  i <- 1
  
  while (convergence > eps && i <= emmax) {
    
    if(is.null(beta) || length(beta) != (ncol(X) - 1)) {
      beta <- rep(0, ncol(X) - 1)
    }
    
    survival  <- drop(s^(exp(X[, -1, drop = FALSE] %*% beta)))
    survival1 <- drop(s1^(exp(X1[, -1, drop = FALSE] %*% beta)))
    
    # E-STEP: Calculate posterior probability
    w_prob <- Status + (1-Status)*(1-((1-UN)^(survival)))
    w_prob <- pmin(pmax(w_prob, 1e-4), 1-1e-4)
    
    # M-STEP: Incidence Part using Data Augmentation (K=5)
    K <- 5
    V_matrix <- matrix(rbinom(n * K, size = 1, prob = rep(w_prob, each = K)), nrow = n, byrow = TRUE)
    
    cure_preds <- matrix(NA_real_, nrow = n, ncol = K)
    pred_preds <- matrix(NA_real_, nrow = m, ncol = K)
    
    for (k in 1:K) {
      yk <- factor(V_matrix[, k], levels = c(0, 1), labels = c("cured", "uncured"))
      
      # --- FIX: Check for at least two classes ---
      if (length(unique(yk)) < 2) {
        # Fallback: if all labels are the same, use the w_prob as the prediction
        cure_preds[, k] <- w_prob
        pred_preds[, k] <- PRED 
        next
      }
      
      mod_data <- data.frame(Z[, -1, drop = FALSE])
      mod_data$yk <- yk
      
      cls_k <- table(yk)
      ss_k  <- pmax(2L, floor(0.75 * cls_k))
      rf_fit <- try(randomForest::randomForest(
        yk ~ ., data = mod_data,
        ntree = best_params$ntree,
        mtry  = best_params$mtry,
        nodesize = 10,
        maxnodes = 10,
        replace = TRUE,
        sampsize = ss_k
      ), silent = TRUE)
      
      if (!inherits(rf_fit, "try-error")) {
        # probs_train <- rf_fit$votes[, "uncured"]
        probs_train <- predict(rf_fit, newdata = as.data.frame(Z[,  -1, drop = FALSE]), type = "prob")
        probs_test  <- predict(rf_fit, newdata = as.data.frame(Z1[, -1, drop = FALSE]), type = "prob")
        cure_preds[, k] <- pmin(pmax(probs_train[, "uncured"], 1e-6), 1 - 1e-6)
        pred_preds[, k] <- pmin(pmax(probs_test[, "uncured"],  1e-6), 1 - 1e-6)
      } else {
        # Fallback to previous values on error
        cure_preds[, k] <- UN
        pred_preds[, k] <- PRED
      }
    }
    
    update_cureb <- rowMeans(cure_preds, na.rm = TRUE)
    update_pred <- rowMeans(pred_preds, na.rm = TRUE)
    
    # Latency updates (CoxPH)
    M <- Status - (survival * log(pmax(1 - update_cureb, 1e-6)))
    M1 <- Status1 - (survival1 * log(pmax(1 - update_pred, 1e-6)))
    
    df_cox <- data.frame(Time = Time, Status = Status, logM = log(pmax(M, 1e-4)))
    X_part <- as.data.frame(X[, -1, drop = FALSE])
    colnames(X_part) <- paste0("V", 1:ncol(X_part))
    df_cox <- cbind(df_cox, X_part)
    
    cox_formula <- as.formula(paste("Surv(Time, Status) ~", paste(colnames(X_part), collapse = "+"), "+ offset(log(pmax(M, 1e-4)))"))
    cox_fit <- try(coxph(cox_formula, data = df_cox, subset = M != 0, method = "breslow"), silent = TRUE)
    
    update_beta <- cox_fit$coefficients
    update_s <- smsurv(Time, Status, X, update_beta, w = M, model = "ph")$survival
    update_s1 <- smsurv(Time1, Status1, X1,update_beta, w = M1, model = "ph")$survival
    
    convergence <- sum((update_beta - beta)^2, na.rm = TRUE) + mean((update_cureb - UN)^2, na.rm = TRUE)
    
    UN <- update_cureb; PRED <- update_pred; beta <- update_beta; s <- update_s; s1 <- update_s1; i <- i + 1
  }
  
  survival_final <- drop(s1 ^ exp(as.vector(X1[, -1, drop = FALSE] %*% beta)))
  Sp = (1-UN)^(1-drop(s ^ exp(as.vector(X[, -1, drop = FALSE] %*% beta))))
  Sp.pred = (1-PRED)^(1-survival_final)
  
  return(list(latencyfit = beta, UN = UN, PRED = PRED, Sp = Sp, Sp.pred = Sp.pred, 
              S.pred = survival_final, s0 = s, iterations = i - 1))
}

smcure.RF.Pois <- function(train, test, Var = TRUE, emmax = 500, eps = 1e-3, ntree_grid = c( 300, 400, 500), mtry_grid = NULL, nboot = 500) {
  Time <- train$t; Status <- train$d
  Time1 <- test$t; Status1 <- test$d
  
  X <- model.matrix(~ x2 + x3 + x4 + x6, data = train)
  X1 <- model.matrix(~ x2 + x3 + x4 + x6, data = test)
  
  # Standardize
  cols_scale <- colnames(X) %in% c("x2", "x6")
  sc <- scale(X[, cols_scale])
  X[, cols_scale] <- sc
  X1[, cols_scale] <- scale(X1[, cols_scale], center = attr(sc, "scaled:center"), scale = attr(sc, "scaled:scale"))
  Z <- X; Z1 <- X1
  
  
  coxfit_train <- coxph(Surv(Time, Status) ~ 1, data = train)
  coxfit_test <- coxph(Surv(Time1, Status1) ~ 1, data = test)
  
  
  out.data <- basehaz(coxfit_train, centered = FALSE)  # columns: hazard, time
  S0_grid <- exp(-out.data[,1])
  
  
  out.data1 <- basehaz( coxfit_test, centered = FALSE)  # columns: hazard, time
  S01_grid <- exp(-out.data1[,1])
  
  s0_init  <- S0_grid # length(Time)
  s01_init <- S01_grid  # length(Time1)
  
  # --- Tuning (Robust to class imbalance) ---
  nw <- factor(Status, levels = c(0,1), labels = c("cured","uncured"))
  Xrf <- as.data.frame(Z[, -1, drop = FALSE])
  if (is.null(mtry_grid)) mtry_grid <- max(1L, floor(sqrt(ncol(Xrf))))
  
  grid <- expand.grid(ntree = ntree_grid, mtry = mtry_grid)
  grid$auc <- NA_real_
  
  # Base R manual folds
  set.seed(123)
  K_folds <- 10
  f_idx <- sample(rep(1:K_folds, length.out = length(Status)))
  
  for (i in 1:nrow(grid)) {
    fold_aucs <- numeric(K_folds)
    for (k in 1:K_folds) {
      va_idx <- which(f_idx == k); tr_idx <- which(f_idx != k)
      y_tr <- nw[tr_idx]; y_va <- nw[va_idx]
      
      if (length(unique(y_tr)) < 2) { fold_aucs[k] <- NA; next }
      
      fit <- try(randomForest::randomForest(x = Xrf[tr_idx,], y = y_tr, ntree = grid$ntree[i], mtry = grid$mtry[i]), silent = TRUE)
      if (inherits(fit, "try-error")) { fold_aucs[k] <- NA; next }
      
      pv <- predict(fit, newdata = Xrf[va_idx,], type = "prob")[, "uncured"]
      # Simple AUC calculation
      y_num <- as.integer(y_va == "uncured")
      r <- rank(pv); n1 <- sum(y_num); n0 <- length(y_num) - n1
      fold_aucs[k] <- if(n1 > 0 && n0 > 0) (sum(r[y_num==1]) - n1*(n1+1)/2) / (n1*n0) else NA
    }
    grid$auc[i] <- mean(fold_aucs, na.rm = TRUE)
  }
  
  best_idx <- if(all(is.na(grid$auc))) 1 else which.max(grid$auc)
  best_params <- list(ntree = grid$ntree[best_idx], mtry = grid$mtry[best_idx])
  
  # Initial probabilities
  init_mod <- randomForest::randomForest(x = Xrf, y = nw, ntree = best_params$ntree, mtry = best_params$mtry)
  uncureprob <- predict(init_mod, type = "prob")[, "uncured"]
  uncurepred <- predict(init_mod, newdata = as.data.frame(Z1[,-1]), type = "prob")[, "uncured"]
  
  emfit <- em.RF.Pois(Time, Status, Time1, Status1, X, X1, Z, Z1, 
                      coxfit_train$coefficients, s0_init, s01_init, 
                      uncureprob, uncurepred, emmax, eps, best_params)
  if (Var) {
    cat("Starting bootstrap (", nboot, " iterations)...\n")
    latency_boot <- matrix(NA_real_, nboot, length(emfit$latencyfit))
    
    
    
    
    for (i in 1:nboot) {
      cat("Bootstrap", i, "of", nboot, "\n")
      boot_idx <- sample(1:nrow(train), replace = TRUE)
      
      Time_b   <- Time[boot_idx]
      Status_b <- Status[boot_idx]
      X_b      <- X[boot_idx, , drop = FALSE]
      Z_b      <- Z[boot_idx, , drop = FALSE]
      
      if (length(unique(Status_b)) < 2) next
      
      boot_train_df <- data.frame(
        t  = Time_b,
        d  = Status_b,
        x2 = X_b[, "x2"],
        x3 = X_b[, "x3"],
        x4 = X_b[, "x4"],
        x6 = X_b[, "x6"]
      )
      
      coxfit_b <- try(
        coxph(Surv(t, d) ~ x2 + x3 + x4 + x6, data = boot_train_df),
        silent = TRUE
      )
      
      if (inherits(coxfit_b, "try-error")) next
      
      bh_b <- basehaz(coxfit_b, centered = FALSE)
      S0_b_grid <- exp(-bh_b$hazard)
      t_grid_b  <- bh_b$time
      
      idx_b <- pmax(1, findInterval(Time_b, t_grid_b))
      s0_b  <- S0_b_grid[idx_b]
      
      if (any(is.na(s0_b))) {
        s0_b[is.na(s0_b)] <- min(s0_b, na.rm = TRUE)
      }
      
      b_fit <- try(
        em.RF.Pois(
          Time_b, Status_b, Time1, Status1,
          X_b, X1, Z_b, Z1,
          emfit$latencyfit,
          s0_b, s01_init,
          uncureprob[boot_idx], uncurepred,
          emmax, eps, best_params
        ),
        silent = TRUE
      )
      
      if (!inherits(b_fit, "try-error")) {
        latency_boot[i, ] <- b_fit$latencyfit
      }
      
    }
    
    cat("Successful RF bootstrap fits:",
        sum(complete.cases(latency_boot)), "out of", nboot, "\n")
    
    emfit$latency_se <- apply(latency_boot, 2, sd, na.rm = TRUE)
    emfit$latency_p  <- 2 * (1 - pnorm(abs(emfit$latencyfit / emfit$latency_se)))
  }
  return(emfit)
}














# --- Data Execution ---
Melanoma <- read.table("~/Desktop/Desktop/melanomadata.txt", header = T)


Melanoma$x3 <- as.numeric(Melanoma$x3)
Melanoma$x4 <- as.numeric(Melanoma$x4)



set.seed(2025)

idx <- createDataPartition(Melanoma$d, p = 0.7, list = FALSE)
train_df <- Melanoma[idx, ]
test_df  <- Melanoma[-idx, ]



methods <- c("Logit","Spline","DT","SVM","NN", "XGB", "RF")




plot_test_rocs_ptcm <- function(methods, train_df, test_df,
                                B =500, emmax = 500, eps = 1e-3,
                                seed_fit = 2025, seed_imp = 790,
                                legend_pos = "bottomright") {
  
  fpr_grid <- seq(0, 1, length.out = 200)
  
  kept <- character(0)
  mean_tpr_list <- list()
  fits <- list()
  auc_mean <- c()
  valid_runs_vec <- c()
  mean_fpr_list <- list()
  
  for (m in methods) {
    cat("\n====================\nMethod:", m, "\n====================\n")
    
    func <- get(paste0("smcure.", m, ".Pois"))
    
    # Fit on TRAIN, predict on TEST
    set.seed(seed_fit)
    out<- try(func(train = train_df, test =test_df, Var = T, emmax = 500, eps = 1e-3, nboot=500),
              silent = TRUE)
    
    if (inherits(out, "try-error")) {
      cat("FAILED during fit for", m, ":\n", as.character(out), "\n")
      next
    }
    
    
    
    fits[[m]] <- out
    
    
    if (!is.null(out$latencyfit) && !is.null(out$latency_se) && !is.null(out$latency_p)) {
      
      print(data.frame(
        term    = names(out$latencyfit),
        beta    = sprintf("%.4f", as.numeric(out$latencyfit)),
        se      = sprintf("%.4f", as.numeric(out$latency_se)),
        p_value = sprintf("%.4f", as.numeric(out$latency_p))
      ))
    }
    
    # ----- Posterior Pr(uncured | observed) on TEST (PTCM) -----
    Status_te <- as.integer(test_df$d)
    PRED   <- as.numeric(out$PRED)
    S_pred <- as.numeric(out$S.pred)
    
    w_post_te <- Status_te + (1 - Status_te) *  (1-(1-PRED)^S_pred)
    w_post <- pmin(pmax(w_post_te, 1e-6), 1 - 1e-6)
    
    # We want ROC for π(x) = Pr(uncured), so:
    pi_hat  <-PRED
    pi_hat  <- pmin(pmax(pi_hat, 1e-6), 1 - 1e-6)
    pi_post <- w_post
    
    
    set.seed(seed_imp)
    thr_grid <- seq(0, 1, length.out = length(Status_te))  
    
    
    V_test_ext <- matrix(
      rbinom(length(w_post) * B, size = 1, prob = rep(w_post, each = B)),
      nrow = length(w_post), byrow = TRUE
    )
    
    
    
    tpr_mat <- matrix(NA_real_, nrow = B, ncol = length(thr_grid))
    fpr_mat <- matrix(NA_real_, nrow = B, ncol = length(thr_grid))
    aucs <- rep(NA_real_, B)
    
    
    pb <- utils::txtProgressBar(min = 0, max = B, style = 3)
    
    for (b in 1:B) {
      C <- V_test_ext[, b]
      if (length(unique(C)) < 2) {
        utils::setTxtProgressBar(pb, b)
        next
      }
      
      r <- pROC::roc(response = C, predictor = pi_hat, quiet = TRUE, direction = "<")
      aucs[b] <- as.numeric(pROC::auc(r))
      
      # stable curve points
      cc <- pROC::coords(
        r,
        x = thr_grid,
        input = "threshold",
        ret = c("threshold", "sensitivity", "specificity"),
        transpose = FALSE
      )
      
      tpr_mat[b, ] <- cc[, "sensitivity"]
      fpr_mat[b, ] <- 1 - cc[, "specificity"]
      
      utils::setTxtProgressBar(pb, b)
    }
    close(pb)
    
    
    
    mean_fpr <- colMeans(fpr_mat, na.rm = TRUE)
    mean_tpr <- colMeans(tpr_mat, na.rm = TRUE)
    
    # --- GUARD AGAINST INVALID ROC (ALL NA / NON-FINITE) ---
    if (!any(is.finite(mean_fpr)) || !any(is.finite(mean_tpr))) {
      cat("Skipping", m, ": no valid ROC points\n")
      next
    }
    
    mean_tpr_list[[m]] <- mean_tpr
    mean_fpr_list[[m]] <- mean_fpr
    
    
    
    
    kept <- c(kept, m)
    mean_tpr_list[[m]] <- colMeans(tpr_mat, na.rm = TRUE)
    auc_mean[m] <- mean(aucs, na.rm = TRUE)
   
    
    
    cat(sprintf("Done %s: TEST mean AUC(π) = %.4f\n", m, auc_mean[m]))
  }
  
  if (length(kept) == 0) stop("No methods succeeded.")
  
  cols <- grDevices::rainbow(length(kept))
  ltys <- rep(1:6, length.out = length(kept))
  
  plot(mean_fpr_list[[kept[1]]], mean_tpr_list[[kept[1]]],
       type = "l", col = cols[1], lty = ltys[1], lwd = 2,
       xlab = "False Positive Rate", ylab = "True Positive Rate",
       main = "")
  
  if (length(kept) > 1) {
    for (k in 2:length(kept)) {
      lines(mean_fpr_list[[kept[k]]], mean_tpr_list[[kept[k]]], col = cols[k], lty = ltys[k], lwd = 2)
    }
  }
  
  legend_labels <- sprintf("%s (AUC=%.4f)", kept, auc_mean[kept])
  legend(legend_pos, legend = legend_labels,
         col = cols, lty = ltys, lwd = 2, bty = "n", cex = 0.85)
 
  invisible(list(methods = kept, auc = auc_mean, 
                 fpr = fpr_grid, tpr = mean_tpr_list))
}



res_test <- plot_test_rocs_ptcm(methods, train_df,test_df, B =500, emmax = 500, eps = 1e-3)

time<-proc.time()-t
time





